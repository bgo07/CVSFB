
"""FrostyRebuild: FBMOD v5 -> FBPROJECT v14 converter.
Regular EBX are reconstructed into project EBX data; RES/CHUNK payloads are preserved.
P1TCW Added RES relationships are inferred from Added EBX names; custom-handler resources remain isolated.
Install: python -m pip install zstandard lz4
"""
import hashlib
import datetime
import io
import json
import queue
import struct
import threading
import uuid
import zlib
from collections import Counter
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk

MAX_EBX_BYTES = 256 * 1024 * 1024
TYPE_NAMES = {0: 'Embedded', 1: 'EBX', 2: 'RES', 3: 'CHUNK', 4: 'Bundle'}


class UnsupportedData(Exception):
    """A known case requiring support that this stage does not implement."""


class Reader:
    """Read bounded binary fields, never silently accept a short read."""
    def __init__(self, file, end):
        self.file, self.end = file, end

    def read(self, size):
        if size < 0 or size > self.end - self.file.tell():
            raise ValueError('Invalid size or unexpected end of file.')
        data = self.file.read(size)
        if len(data) != size:
            raise ValueError('The file ended unexpectedly.')
        return data

    def number(self, fmt):
        return struct.unpack('<' + fmt, self.read(struct.calcsize('<' + fmt)))[0]

    def text(self):
        data = bytearray()
        while True:
            byte = self.read(1)
            if byte == b'\0':
                return data.decode('utf-8')
            data.extend(byte)
            if len(data) > 1_000_000:
                raise ValueError('Invalid text field.')


def decompress_cas(data, expected_size):
    """Decode Frostbite CAS blocks. Preserve original RES/CHUNK bytes elsewhere."""
    if expected_size < 0 or expected_size > MAX_EBX_BYTES:
        raise UnsupportedData('EBX exceeds the 256 MiB analysis limit.')
    reader = Reader(io.BytesIO(data), len(data))
    output = bytearray()
    codecs = set()
    while reader.file.tell() < reader.end:
        header = reader.read(8)
        size_field = struct.unpack_from('>I', header)[0]
        compression = struct.unpack_from('<H', header, 4)[0]
        stored_size = struct.unpack_from('>H', header, 6)[0]
        stored_size += ((compression >> 8) & 15) << 16
        output_size = size_field & 0xFFFFFF
        codec = compression & 0x7F
        if size_field & 0xFF000000:
            raise UnsupportedData('CAS block requires an external dictionary.')
        if compression & 0x80:
            raise UnsupportedData('Obfuscated CAS block is not supported.')
        if len(output) + output_size > expected_size:
            raise ValueError('CAS output exceeds the declared resource size.')
        block = reader.read(stored_size)
        if codec == 0:
            decoded = block
            codecs.add('Uncompressed')
        elif codec == 2:
            decoder = zlib.decompressobj()
            decoded = decoder.decompress(block, output_size + 1)
            if not decoder.eof or decoder.unused_data or decoder.unconsumed_tail:
                raise ValueError('Invalid or oversized Zlib block.')
            codecs.add('Zlib')
        elif codec == 15:
            try:
                import zstandard
            except ImportError:
                raise UnsupportedData('Install zstandard: python -m pip install zstandard')
            parameters = zstandard.get_frame_parameters(block)
            if parameters.dict_id:
                raise UnsupportedData('Zstandard frame requires an external dictionary.')
            if parameters.content_size not in (zstandard.CONTENTSIZE_UNKNOWN, output_size):
                raise ValueError('Zstandard frame size differs from CAS header.')
            # Bounded read also protects frames with an unknown content size.
            with zstandard.ZstdDecompressor().stream_reader(io.BytesIO(block)) as stream:
                decoded = stream.read(output_size + 1)
                if stream.read(1):
                    raise ValueError('Oversized Zstandard frame.')
            codecs.add('Zstandard')
        elif codec == 9:
            try:
                import lz4.block
            except ImportError:
                raise UnsupportedData('Install lz4: python -m pip install lz4')
            decoded = lz4.block.decompress(block, uncompressed_size=output_size)
            codecs.add('LZ4')
        else:
            raise UnsupportedData(f'CAS compression 0x{codec:02X} is not supported.')
        if len(decoded) != output_size:
            raise ValueError('Decompressed block size differs from CAS header.')
        output.extend(decoded)
    if len(output) != expected_size:
        raise ValueError('Decompressed resource size differs from FBMOD metadata.')
    return bytes(output), sorted(codecs)


def inspect_ebx(data):
    """Conservative structural screening, not proof that Frosty can load the asset."""
    if len(data) < 64:
        raise ValueError('EBX header is incomplete.')
    magic, strings_offset, strings_data_size, import_count = struct.unpack_from('<4I', data)
    if magic not in (0x0FB2D1CE, 0x0FB4D1CE):
        raise UnsupportedData(f'EBX signature 0x{magic:08X} requires another reader.')
    instances, exported, unique, classes, fields, names_size = struct.unpack_from('<6H', data, 16)
    strings_size, arrays, data_size = struct.unpack_from('<3I', data, 28)
    result = {
        'ebx_version': 2 if magic == 0x0FB2D1CE else 4,
        'file_guid': str(uuid.UUID(bytes_le=data[40:56])),
        'class_count': classes, 'field_count': fields,
        'import_count': import_count,
    }
    if not classes or not names_size:
        raise UnsupportedData('No embedded class/name tables; external schema or another EBX reader may be required.')
    names_start = 64 + import_count * 32
    fields_start = names_start + names_size
    classes_start = fields_start + fields * 16
    instances_start = classes_start + classes * 16
    table_end = instances_start + instances * 4
    table_end = (table_end + 15) // 16 * 16
    table_end += arrays * 12
    table_end = (table_end + 15) // 16 * 16
    if magic == 0x0FB4D1CE:
        boxed_count, boxed_offset = struct.unpack_from('<2I', data, 56)
        if boxed_count:
            table_end = (table_end + 15) // 16 * 16 + boxed_count * 8
            if strings_offset + strings_size + boxed_offset > len(data):
                raise ValueError('Boxed value offset exceeds EBX size.')
    if table_end > strings_offset or strings_offset > len(data):
        raise ValueError('EBX tables overlap data or exceed the file.')
    if strings_offset + strings_data_size > len(data):
        raise ValueError('EBX strings/data section exceeds the file.')
    if strings_size + data_size > strings_data_size:
        raise ValueError('EBX string/data sizes are inconsistent.')
    if exported > instances or unique > classes or instances == 0:
        raise ValueError('EBX instance counts are inconsistent.')
    # Resolve embedded class/field names with the hash used by EbxReader.
    def name_hash(text):
        value = 5381
        for char in text:
            value = ((value * 33) ^ (ord(char) & 0xFF)) & 0xFFFFFFFF
        return value
    names = {}
    raw_names = data[names_start:fields_start]
    if not raw_names.endswith(b'\0'):
        raise ValueError('EBX name table is not null-terminated.')
    for raw in raw_names.split(b'\0'):
        if raw:
            name = raw.decode('utf-8')
            names[name_hash(name)] = name
    class_names = []
    for i in range(classes):
        pos = classes_start + i * 16
        hash_value, field_index = struct.unpack_from('<Ii', data, pos)
        field_count, alignment = struct.unpack_from('<BB', data, pos + 8)
        if hash_value not in names:
            raise ValueError('Class name hash is absent from the EBX name table.')
        if field_index < 0 or field_index + field_count > fields:
            raise ValueError('Class field range exceeds the EBX field table.')
        if alignment not in (1, 2, 4, 8, 16):
            raise UnsupportedData(f'Class alignment {alignment} needs further analysis.')
        class_names.append(names[hash_value])
    for i in range(fields):
        field_hash = struct.unpack_from('<I', data, fields_start + i * 16)[0]
        if field_hash not in names:
            raise ValueError('Field name hash is absent from the EBX name table.')
    for i in range(instances):
        class_index, count = struct.unpack_from('<HH', data, instances_start + i * 4)
        if class_index >= classes or count == 0:
            raise ValueError('Invalid EBX instance descriptor.')
    first_class = struct.unpack_from('<H', data, instances_start)[0]
    result['root_type'] = class_names[first_class]
    result['classes'] = class_names
    result['status'] = 'candidate'
    result['note'] = 'Embedded tables passed structural screening; Frosty type resolution and serialization remain untested.'
    return result


def read_fbmod(path, progress=lambda text: None):
    resources = []
    with open(path, 'rb') as file:
        size = file.seek(0, 2)
        file.seek(0)
        r = Reader(file, size)
        if r.read(8) != b'FROSTY\0\1':
            raise ValueError('Invalid FBMOD signature.')
        version = r.number('I')
        if version != 5:
            raise ValueError(f'FBMOD format {version}: only format 5 is supported.')
        table_offset, block_count = r.number('q'), r.number('i')
        payload_start = table_offset + block_count * 16
        if block_count < 0 or table_offset < file.tell() or payload_start > size:
            raise ValueError('Invalid FBMOD data table.')
        r.end = table_offset
        game = r.read(r.number('B')).decode('utf-8')
        game_version = r.number('I')
        info = {key: r.text() for key in ('Name', 'Author', 'Category', 'Mod version', 'Description', 'Link')}
        info.update({'Game': game, 'Game version': game_version, 'FBMOD format': version})
        count = r.number('i')
        if count < 0 or count > (table_offset - file.tell()) // 10:
            raise ValueError('Invalid resource count.')
        for i in range(count):
            t, index, name = r.number('B'), r.number('i'), r.text()
            if t not in TYPE_NAMES or index < -1 or index >= block_count:
                raise ValueError(f'Invalid resource descriptor {i}.')
            asset = dict(type=t, name=name, data_index=index, sha1=None, flags=0, handler=0, user_data='')
            if index != -1:
                asset.update(sha1=r.read(20).hex(), original_size=r.number('q'), flags=r.number('B'), handler=r.number('i'), user_data=r.text())
            n = r.number('i')
            if n < 0 or n > (r.end - file.tell()) // 4:
                raise ValueError('Invalid bundle count.')
            asset['added_bundles'] = [r.number('i') for _ in range(n)]
            if t == 2:
                asset.update(res_type=r.number('I'), res_id=r.number('Q'))
                asset['metadata'] = r.read(r.number('i')).hex()
            elif t == 3:
                for key in ('range_start', 'range_end', 'logical_offset', 'logical_size'):
                    asset[key] = r.number('I')
                asset.update(name_hash=r.number('i'), first_mip=r.number('i'))
            elif t == 4:
                asset.update(bundle_name=r.text(), superbundle_hash=r.number('i'))
            resources.append(asset)
        if file.tell() != table_offset:
            raise ValueError('Resource table did not end at the expected offset.')
        r.end = size
        blocks = []
        for i in range(block_count):
            offset, length = r.number('q'), r.number('q')
            if offset < 0 or length < 0 or payload_start + offset + length > size:
                raise ValueError(f'Invalid data block {i}.')
            blocks.append((payload_start + offset, length))
        hashes, verified = {}, 0
        for i, asset in enumerate(resources):
            index = asset['data_index']
            if index == -1:
                continue
            offset, length = blocks[index]
            asset.update(offset=offset, stored_size=length)
            if asset['type'] not in (1, 2, 3):
                continue
            if index not in hashes:
                progress(f'Checking data integrity: {i + 1}/{count}')
                file.seek(offset)
                h, remaining = hashlib.sha1(), length
                while remaining:
                    chunk = r.read(min(1024 * 1024, remaining))
                    h.update(chunk)
                    remaining -= len(chunk)
                hashes[index] = h.hexdigest()
            if hashes[index] != asset['sha1']:
                raise ValueError('SHA-1 mismatch: ' + asset['name'])
            verified += 1
        ebx_assets = [a for a in resources if a['type'] == 1]
        for i, asset in enumerate(ebx_assets):
            progress(f'Analyzing EBX: {i + 1}/{len(ebx_assets)}')
            if asset['data_index'] == -1:
                asset['ebx'] = dict(status='no_payload', note='Requires an existing game asset; no EBX payload in this mod.')
                continue
            if asset['handler']:
                asset['ebx'] = dict(status='custom_handler', note='Handler data is not treated as a complete EBX file.')
                continue
            analysis = {}
            try:
                if asset['stored_size'] > MAX_EBX_BYTES:
                    raise UnsupportedData('Stored EBX exceeds the 256 MiB analysis limit.')
                file.seek(asset['offset'])
                raw, codecs = decompress_cas(r.read(asset['stored_size']), asset['original_size'])
                analysis.update(decompressed=True, decompressed_size=len(raw), codecs=codecs)
                analysis.update(inspect_ebx(raw))
            except UnsupportedData as error:
                analysis.update(status='unsupported', note=str(error))
            except Exception as error:
                analysis.update(status='analysis_error', note=str(error))
            asset['ebx'] = analysis
    counts = Counter(TYPE_NAMES[a['type']] for a in resources)
    states = Counter(a['ebx']['status'] for a in ebx_assets)
    info.update({'Total resource entries': count, 'Data blocks': block_count})
    info.update({name: counts[name] for name in TYPE_NAMES.values()})
    info.update({'Entries marked as added': sum(bool(a['flags'] & 8) for a in resources),
                 'Entries with custom handlers': sum(bool(a['handler']) for a in resources),
                 'Verified resource entries': verified, 'Unique blocks verified': len(hashes),
                 'Data integrity': 'SHA-1 checks passed' if verified else 'No resource payloads verified',
                 'EBX decompressed': sum(bool(a['ebx'].get('decompressed')) for a in ebx_assets)})
    for state in ('candidate', 'custom_handler', 'no_payload', 'unsupported', 'analysis_error'):
        info['EBX ' + state] = states[state]
    info['Stage'] = 'Analysis only. No FBPROJECT generated.'
    return info, resources



PROJECT_MAGIC = 0x00005954534F5246
PROJECT_VERSION = 14


class BinaryWriter:
    def __init__(self, file):
        self.file = file

    def raw(self, data):
        self.file.write(data)

    def i32(self, value):
        self.file.write(struct.pack('<i', int(value)))

    def u32(self, value):
        self.file.write(struct.pack('<I', int(value) & 0xFFFFFFFF))

    def i64(self, value):
        self.file.write(struct.pack('<q', int(value)))

    def u64(self, value):
        self.file.write(struct.pack('<Q', int(value) & 0xFFFFFFFFFFFFFFFF))

    def boolean(self, value):
        self.file.write(struct.pack('<?', bool(value)))

    def text(self, value):
        self.file.write(str(value or '').encode('utf-8') + b'\0')

    def guid(self, value):
        guid = value if isinstance(value, uuid.UUID) else uuid.UUID(str(value))
        self.file.write(guid.bytes_le)

    def sha1(self, hex_value):
        data = bytes.fromhex(hex_value)
        if len(data) != 20:
            raise ValueError('Invalid SHA-1 length.')
        self.file.write(data)

    def counted(self, callback):
        pos = self.file.tell()
        self.i32(0)
        count = callback()
        end = self.file.tell()
        self.file.seek(pos)
        self.i32(count)
        self.file.seek(end)


def dotnet_ticks_now():
    now = datetime.datetime.now()
    epoch = datetime.datetime(1, 1, 1)
    delta = now - epoch
    return (
        delta.days * 24 * 60 * 60 * 10_000_000
        + delta.seconds * 10_000_000
        + delta.microseconds * 10
    )


def fnv1_hash(text):
    value = 0x811C9DC5
    for byte in text.lower().encode('utf-8'):
        value = (value * 0x01000193) & 0xFFFFFFFF
        value ^= byte
    return value if value < 0x80000000 else value - 0x100000000


def bundle_hash(name):
    name = str(name).lower()
    if len(name) == 8:
        try:
            value = int(name, 16)
            return value if value < 0x80000000 else value - 0x100000000
        except ValueError:
            pass
    return fnv1_hash(name)


def build_bundle_name_map(resources):
    result = {bundle_hash('chunks'): 'chunks'}
    for asset in resources:
        if asset['type'] != 4:
            continue
        for candidate in (asset.get('name'), asset.get('bundle_name')):
            if candidate:
                result[bundle_hash(candidate)] = candidate
    return result


def resolve_added_bundles(asset, bundle_names, warnings):
    names = []
    seen = set()
    for value in asset.get('added_bundles', []):
        name = bundle_names.get(value)
        if name is None:
            warnings.add(
                f"Bundle hash 0x{value & 0xFFFFFFFF:08X} used by {asset['name']} "
                "could not be resolved to a bundle name."
            )
            continue
        if name not in seen:
            seen.add(name)
            names.append(name)
    return names


def read_payload(file, asset):
    if asset.get('data_index', -1) == -1:
        return None
    file.seek(asset['offset'])
    data = file.read(asset['stored_size'])
    if len(data) != asset['stored_size']:
        raise ValueError(f"The file ended unexpectedly while reading {asset['name']}.")
    return data


def prepare_project_assets(fbmod_path, resources, progress=lambda text: None):
    bundle_names = build_bundle_name_map(resources)
    warnings = set()

    # FBMOD quirk seen in P1TCW-style mods:
    # newly-created EBX entries carry IsAdded (0x08), but their paired RES entries
    # often do not. A project must still register those RES entries under Added RES
    # or FrostyProject.InternalLoad() cannot find them by name/RID later.
    added_ebx_names = {
        a['name'].lower()
        for a in resources
        if a['type'] == 1 and (a.get('flags', 0) & 0x08)
    }

    def res_belongs_to_added_ebx(res_name):
        name = res_name.lower()

        # Texture/MeshSet RES commonly has exactly the same asset name as its EBX.
        if name in added_ebx_names:
            return True

        # Mesh shader-block RES commonly uses:
        #   <mesh-ebx-name>_mesh/blocks
        suffix = '_mesh/blocks'
        if name.endswith(suffix):
            parent_ebx = name[:-len(suffix)]
            if parent_ebx in added_ebx_names:
                return True

        return False

    project = {
        'added_ebx': [],
        'added_res': [],
        'added_chunks': [],
        'modified_ebx': [],
        'modified_res': [],
        'modified_chunks': [],
        'skipped_handlers': [],
        'warnings': warnings,
    }

    with open(fbmod_path, 'rb') as file:
        ebx_total = sum(a['type'] == 1 for a in resources)
        ebx_done = 0

        for asset in resources:
            t = asset['type']
            is_added = bool(asset.get('flags', 0) & 0x08)
            bundles = resolve_added_bundles(asset, bundle_names, warnings)

            if t == 1:
                ebx_done += 1
                progress(f'Preparing EBX for project: {ebx_done}/{ebx_total}')

                # IMPORTANT:
                # A custom-handler payload inside an FBMOD is the input of
                # ICustomActionHandler.Load(...). It is NOT the byte format returned
                # by ModifiedResource.Save(), so it cannot be copied directly into
                # an FBPROJECT with modifiedResource=true.
                if asset.get('handler'):
                    project['skipped_handlers'].append({
                        'type': 'EBX',
                        'name': asset['name'],
                        'handler': asset.get('handler', 0),
                        'handler_hex': f"0x{asset.get('handler', 0) & 0xFFFFFFFF:08X}",
                        'flags': asset.get('flags', 0),
                        'is_added': bool(asset.get('flags', 0) & 0x08),
                        'stored_size': asset.get('stored_size', 0),
                        'original_size': asset.get('original_size', 0),
                        'user_data': asset.get('user_data', ''),
                    })
                    warnings.add(
                        f"Custom-handler EBX requires handler-specific conversion "
                        f"({asset.get('handler', 0) & 0xFFFFFFFF:08X}): {asset['name']}"
                    )
                    continue

                payload = None
                if asset['data_index'] != -1:
                    stored = read_payload(file, asset)
                    payload, _ = decompress_cas(stored, asset['original_size'])
                    ebx_info = asset.get('ebx', {})
                    if ebx_info.get('status') != 'candidate':
                        warnings.add(
                            f"EBX skipped because structural status is "
                            f"{ebx_info.get('status')}: {asset['name']}"
                        )
                        continue

                if is_added:
                    if payload is None:
                        warnings.add(f'Added EBX has no payload and was skipped: {asset["name"]}')
                        continue
                    file_guid = asset.get('ebx', {}).get('file_guid')
                    if not file_guid:
                        warnings.add(f'Added EBX has no resolved GUID and was skipped: {asset["name"]}')
                        continue
                    project['added_ebx'].append({
                        'name': asset['name'],
                        'guid': file_guid,
                    })

                project['modified_ebx'].append({
                    'name': asset['name'],
                    'bundles': bundles,
                    'has_data': payload is not None,
                    'user_data': asset.get('user_data', ''),
                    'data': payload,
                    'custom_handler': False,
                })

            elif t == 2:
                payload = read_payload(file, asset) if asset['data_index'] != -1 else None
                metadata = bytes.fromhex(asset.get('metadata', ''))
                custom_handler = bool(asset.get('handler'))

                # Do not trust only the FBMOD 0x08 flag for RES.
                # Pair RES with an Added EBX when their names/mesh-block relation match.
                inferred_added_res = is_added or res_belongs_to_added_ebx(asset['name'])

                if inferred_added_res and not is_added:
                    warnings.add(
                        f'RES inferred as Added from Added EBX relationship: {asset["name"]}'
                    )

                if custom_handler:
                    project['skipped_handlers'].append({
                        'type': 'RES',
                        'name': asset['name'],
                        'handler': asset.get('handler', 0),
                        'handler_hex': f"0x{asset.get('handler', 0) & 0xFFFFFFFF:08X}",
                        'flags': asset.get('flags', 0),
                        'is_added': bool(asset.get('flags', 0) & 0x08),
                        'res_type': asset.get('res_type', 0),
                        'res_id': asset.get('res_id', 0),
                        'metadata': asset.get('metadata', ''),
                        'stored_size': asset.get('stored_size', 0),
                        'original_size': asset.get('original_size', 0),
                        'user_data': asset.get('user_data', ''),
                    })
                    warnings.add(
                        f"Custom-handler RES requires handler-specific conversion "
                        f"({asset.get('handler', 0) & 0xFFFFFFFF:08X}): {asset['name']}"
                    )
                    # Do NOT write raw handler payload as normal RES and do NOT set
                    # SHA1.Zero. Both would misrepresent the project data.
                    continue

                if inferred_added_res:
                    if len(metadata) != 16:
                        warnings.add(
                            f'Added RES meta is {len(metadata)} bytes instead of 16; '
                            f'not registered as Added RES: {asset["name"]}'
                        )
                    else:
                        project['added_res'].append({
                            'name': asset['name'],
                            'rid': asset['res_id'],
                            'res_type': asset['res_type'],
                            'metadata': metadata,
                        })

                project['modified_res'].append({
                    'name': asset['name'],
                    'bundles': bundles,
                    'has_data': payload is not None,
                    'sha1': asset.get('sha1'),
                    'original_size': asset.get('original_size', 0),
                    'metadata': metadata,
                    'user_data': asset.get('user_data', ''),
                    'data': payload,
                    'custom_handler': False,
                })

            elif t == 3:
                payload = read_payload(file, asset) if asset['data_index'] != -1 else None
                try:
                    chunk_guid = str(uuid.UUID(asset['name']))
                except Exception:
                    warnings.add(f'Invalid CHUNK GUID; skipped: {asset["name"]}')
                    continue

                project['modified_chunks'].append({
                    'guid': chunk_guid,
                    'bundles': bundles,
                    'first_mip': asset.get('first_mip', -1),
                    'h32': asset.get('name_hash', 0),
                    'has_data': payload is not None,
                    'sha1': asset.get('sha1'),
                    'logical_offset': asset.get('logical_offset', 0),
                    'logical_size': asset.get('logical_size', 0),
                    'range_start': asset.get('range_start', 0),
                    'range_end': asset.get('range_end', 0),
                    'add_to_chunk_bundle': bool(asset.get('flags', 0) & 0x02),
                    'user_data': asset.get('user_data', ''),
                    'data': payload,
                })

    return project


def write_fbproject(fbmod_path, output_path, info, resources, progress=lambda text: None):
    progress('Building FBPROJECT resource tables...')
    project = prepare_project_assets(fbmod_path, resources, progress)

    def unique(items, key, label):
        out = []
        seen = set()
        for item in items:
            k = key(item)
            if k in seen:
                raise ValueError(f'Duplicate {label}: {k}')
            seen.add(k)
            out.append(item)
        return out

    project['added_ebx'] = unique(project['added_ebx'], lambda x: x['name'].lower(), 'Added EBX name')
    project['added_res'] = unique(project['added_res'], lambda x: x['rid'], 'Added RES RID')
    project['modified_ebx'] = unique(project['modified_ebx'], lambda x: x['name'].lower(), 'Modified EBX name')
    project['modified_res'] = unique(project['modified_res'], lambda x: x['name'].lower(), 'Modified RES name')
    project['modified_chunks'] = unique(project['modified_chunks'], lambda x: x['guid'].lower(), 'Modified CHUNK GUID')

    ticks = dotnet_ticks_now()
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with open(output_path, 'wb') as raw:
        w = BinaryWriter(raw)

        w.u64(PROJECT_MAGIC)
        w.u32(PROJECT_VERSION)
        w.text(info['Game'])
        w.i64(ticks)
        w.i64(ticks)
        w.u32(info['Game version'])

        w.text(info.get('Name', ''))
        w.text(info.get('Author', ''))
        w.text(info.get('Category', ''))
        w.text(info.get('Mod version', ''))
        w.text(info.get('Description', ''))

        w.i32(0)
        for _ in range(4):
            w.i32(0)

        w.i32(0)  # added superbundles
        w.i32(0)  # added bundles

        def write_added_ebx():
            for entry in project['added_ebx']:
                w.text(entry['name'])
                w.guid(entry['guid'])
            return len(project['added_ebx'])
        w.counted(write_added_ebx)

        def write_added_res():
            for entry in project['added_res']:
                w.text(entry['name'])
                w.u64(entry['rid'])
                w.u32(entry['res_type'])
                if len(entry['metadata']) != 16:
                    raise ValueError(f'Added RES metadata must be 16 bytes: {entry["name"]}')
                w.raw(entry['metadata'])
            return len(project['added_res'])
        w.counted(write_added_res)

        w.i32(0)  # Added CHUNK = 0, hybrid-safe

        def write_modified_ebx():
            for entry in project['modified_ebx']:
                w.text(entry['name'])
                w.i32(0)
                w.i32(len(entry['bundles']))
                for bundle in entry['bundles']:
                    w.text(bundle)

                w.boolean(entry['has_data'])
                if entry['has_data']:
                    w.boolean(False)
                    w.text(entry['user_data'])
                    w.boolean(False)
                    w.i32(len(entry['data']))
                    w.raw(entry['data'])
            return len(project['modified_ebx'])
        w.counted(write_modified_ebx)

        def write_modified_res():
            for entry in project['modified_res']:
                w.text(entry['name'])
                w.i32(0)
                w.i32(len(entry['bundles']))
                for bundle in entry['bundles']:
                    w.text(bundle)

                w.boolean(entry['has_data'])
                if entry['has_data']:
                    w.sha1(entry['sha1'])
                    w.i64(entry['original_size'])
                    w.i32(len(entry['metadata']))
                    w.raw(entry['metadata'])
                    w.text(entry['user_data'])
                    w.i32(len(entry['data']))
                    w.raw(entry['data'])
            return len(project['modified_res'])
        w.counted(write_modified_res)

        def write_modified_chunks():
            for entry in project['modified_chunks']:
                w.guid(entry['guid'])
                w.i32(len(entry['bundles']))
                for bundle in entry['bundles']:
                    w.text(bundle)

                w.i32(entry['first_mip'])
                w.i32(entry['h32'])
                w.boolean(entry['has_data'])

                if entry['has_data']:
                    w.sha1(entry['sha1'])
                    w.u32(entry['logical_offset'])
                    w.u32(entry['logical_size'])
                    w.u32(entry['range_start'])
                    w.u32(entry['range_end'])
                    w.boolean(entry['add_to_chunk_bundle'])
                    w.text(entry['user_data'])
                    w.i32(len(entry['data']))
                    w.raw(entry['data'])
            return len(project['modified_chunks'])
        w.counted(write_modified_chunks)

        w.i32(1)
        w.text('legacy')
        w.i32(0)

    inferred_added_res_count = sum(
        1 for warning in project['warnings']
        if warning.startswith('RES inferred as Added from Added EBX relationship:')
    )

    return {
        'output': str(output_path),
        'added_ebx': len(project['added_ebx']),
        'added_res': len(project['added_res']),
        'inferred_added_res': inferred_added_res_count,
        'added_chunks': 0,
        'modified_ebx': len(project['modified_ebx']),
        'modified_res': len(project['modified_res']),
        'modified_chunks': len(project['modified_chunks']),
        'custom_handlers': project['skipped_handlers'],
        'custom_handler_count': len(project['skipped_handlers']),
        'warnings': sorted(project['warnings']),
    }


def main():
    window = tk.Tk()
    window.title('FrostyRebuild - FBMOD to FBPROJECT')
    window.geometry('850x650')
    events, report = queue.Queue(), {}
    status = tk.StringVar(value='Select an FBMOD to convert.')
    toolbar = ttk.Frame(window, padding=10)
    toolbar.pack(fill='x')
    text = scrolledtext.ScrolledText(window, wrap='word', font=('Consolas', 10))
    text.pack(fill='both', expand=True, padx=10, pady=10)
    ttk.Label(window, textvariable=status, padding=10).pack(fill='x')

    def work(path, output_path):
        try:
            info, resources = read_fbmod(path, lambda value: events.put(('progress', value)))
            summary = write_fbproject(
                path,
                output_path,
                info,
                resources,
                lambda value: events.put(('progress', value))
            )
            events.put(('done', {
                'source': str(path),
                'output': str(output_path),
                'info': info,
                'resources': resources,
                'summary': summary
            }))
        except Exception as error:
            events.put(('error', str(error)))

    def select():
        path = filedialog.askopenfilename(parent=window, filetypes=[('Frosty Mod', '*.fbmod')])
        if not path:
            return
        output_path = filedialog.asksaveasfilename(
            parent=window,
            initialfile=Path(path).stem + '.fbproject',
            defaultextension='.fbproject',
            filetypes=[('Frosty Project', '*.fbproject')]
        )
        if not output_path:
            return
        report.clear()
        open_button.config(state='disabled')
        save_button.config(state='disabled')
        text.delete('1.0', 'end')
        status.set('Reading, verifying and converting...')
        threading.Thread(target=work, args=(path, output_path), daemon=True).start()

    def save_report():
        path = filedialog.asksaveasfilename(parent=window, initialfile='FrostyRebuild_EBX_report.json', defaultextension='.json', filetypes=[('JSON report', '*.json')])
        if path:
            try:
                Path(path).write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
                status.set('Report saved.')
            except Exception as error:
                messagebox.showerror('Save error', str(error), parent=window)

    def poll():
        while True:
            try:
                kind, value = events.get_nowait()
            except queue.Empty:
                break
            if kind == 'progress':
                status.set(value)
            else:
                open_button.config(state='normal')
                if kind == 'error':
                    status.set('Analysis stopped.')
                    messagebox.showerror('Read error', value, parent=window)
                else:
                    report.update(value)
                    text.insert('end', '\n'.join(f'{k}: {v}' for k, v in value['info'].items()))
                    summary = value['summary']
                    text.insert('end', '\n\nFBPROJECT RESULT\n')
                    text.insert('end', f"Output: {summary['output']}\n")
                    text.insert('end', f"Added EBX: {summary['added_ebx']}\n")
                    text.insert('end', f"Added RES: {summary['added_res']}\n")
                    text.insert('end', f"  Inferred Added RES: {summary['inferred_added_res']}\n")
                    text.insert('end', f"Added CHUNK: {summary['added_chunks']} (hybrid-safe)\n")
                    text.insert('end', f"Modified EBX: {summary['modified_ebx']}\n")
                    text.insert('end', f"Modified RES: {summary['modified_res']}\n")
                    text.insert('end', f"Modified CHUNK: {summary['modified_chunks']}\n")
                    if summary['warnings']:
                        text.insert('end', '\nWARNINGS\n')
                        for warning in summary['warnings']:
                            text.insert('end', '- ' + warning + '\n')
                    status.set('Conversion complete. Test the FBPROJECT in Frosty.')
                    save_button.config(state='normal')
        window.after(100, poll)

    open_button = ttk.Button(toolbar, text='Convert FBMOD', command=select)
    open_button.pack(side='left')
    save_button = ttk.Button(toolbar, text='Save report', command=save_report, state='disabled')
    save_button.pack(side='left', padx=10)
    poll()
    window.mainloop()


if __name__ == '__main__':
    main()
