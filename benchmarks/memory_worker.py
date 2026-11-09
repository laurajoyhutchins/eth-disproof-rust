"""One fresh Linux process, one case invocation, one peak-RSS observation."""
from __future__ import annotations

import argparse
import json
import os
import resource
import sys
import time
from .cases import prepare_case, CASE_IDS


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, choices=CASE_IDS)
    args = parser.parse_args()
    try:
        import native_ring  # noqa: F401  required, rather than silently falling back
        case = prepare_case(args.case)
        rss_before = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
        result = case.validate()
        rss_after = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
        print(json.dumps({
            'schema_version': '1.0.0',
            'case_id': args.case,
            'parameters': case.parameters,
            'expected': case.expected,
            'actual': result,
            'verified': True,
            'metric': {'name': 'benchmark.memory.peak', 'unit': 'By',
                       'instrument': 'gauge', 'value': rss_after},
            'baseline_rss': {'unit': 'By', 'value': rss_before},
            'operation_count': {'name': 'benchmark.operations', 'unit': '{operation}', 'value': 1},
            'process': {'pid': os.getpid(), 'rusage': 'RUSAGE_SELF',
                        'linux_ru_maxrss_unit': 'KiB'},
        }, sort_keys=True))
        return 0
    except Exception as exc:
        print(f'{type(exc).__name__}: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
