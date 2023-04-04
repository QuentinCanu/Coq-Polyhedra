#! /usr/bin/env python3

# --------------------------------------------------------------------
import sys, os, json

# --------------------------------------------------------------------
sys.path.append(os.path.realpath(os.path.join(
    os.path.dirname(__file__),
    *'../../binreader/scripts'.split('/')
)))

import binreader

# --------------------------------------------------------------------
DESCRIPTORS = dict(
    A = "[[Q]]",
    b = "[Q]",
    bases = "[[I]]",
    idx = "I",
    inv = "[[Q]]",
    steps = "I",
    order = "[I]",
    pred = "[(I,I,I)]",
    pred_vect = "[[[Q]]]",
    vtx = "[[Q]]"
)

DESCRIPTORS = {
    k: binreader.descriptor_of_string(v) for k, v in DESCRIPTORS.items()
}

# --------------------------------------------------------------------
def _main():
    if len(sys.argv)-1 != 1:
        print('Usage: convert [file]', file = sys.stderr)
        exit(1)

    name = sys.argv[1]
    srcdir = os.path.join(os.path.dirname(__file__), '..', 'data', name)
    bindir = os.path.join(srcdir, 'bin')

    os.makedirs(bindir, exist_ok = True)

    with open(os.path.join(srcdir, f'{name}.json')) as stream:
        contents = json.load(stream)

    for key, descr in DESCRIPTORS.items():
        if key not in contents:
            print(f'Ignoring {key}', file = sys.stderr)
            continue
        with open(os.path.join(bindir, f'{key}.bin'), 'w+b') as stream:
            descr.descriptor(stream)
            descr.pickle(contents[key], stream)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
