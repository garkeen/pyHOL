"""Client for the resident holpy REPL server (repl.repl --serve).

One request per invocation: sends the given command lines, prints the
captured output, and exits with a status code (0 = no failure and no open
goal, 1 = a step failed or goals remain, 2 = cannot reach the server).

Usage
=====
    python -m repl.client "theory nat" "goal 0 + n = n" "check"
    python -m repl.client --port 5599 --stdin < cmds.txt
"""

import argparse
import json
import socket
import sys

ROOT = None


def main():
    ap = argparse.ArgumentParser(description='holpy REPL client')
    ap.add_argument('cmds', nargs='*', help='REPL command lines')
    ap.add_argument('--port', type=int, default=5599)
    ap.add_argument('--stdin', action='store_true',
                    help='read command lines from stdin')
    args = ap.parse_args()

    cmds = list(args.cmds)
    if args.stdin:
        cmds.extend(sys.stdin.read().splitlines())

    payload = json.dumps({'cmds': cmds}).encode('utf-8') + b'\n'
    try:
        s = socket.create_connection(('127.0.0.1', args.port), timeout=600)
    except OSError as e:
        print('cannot reach REPL server on port %d: %s' % (args.port, e))
        sys.exit(2)
    s.sendall(payload)
    with s.makefile('rb') as f:
        raw = f.readline()
    s.close()
    if not raw:
        print('no reply from REPL server')
        sys.exit(2)
    resp = json.loads(raw.decode('utf-8'))
    sys.stdout.write(resp.get('out', ''))
    gaps = resp.get('gaps')
    if gaps:
        print('open goals: %d' % gaps)
    if resp.get('failed') or gaps:
        sys.exit(1)


if __name__ == '__main__':
    main()
