"""One benchmark operation per fresh Linux process, exact peak-RSS in bytes."""
from __future__ import annotations
import argparse,json,resource,os,sys
from .native_dlx_cases import prepare

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',required=True)
    ap.add_argument('--variant',required=True)
    args=ap.parse_args()
    case=prepare(args.case,args.variant)
    operation=case.operation_factory()
    before=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
    result=operation()
    after=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
    if result!=case.expected:
        raise AssertionError(f'{case.case_id}/{case.variant}: {result!r} != {case.expected!r}')
    print(json.dumps({'schema_version':'1.0.0','case_id':case.case_id,
        'variant':case.variant,'parameters':case.parameters,'verified':True,
        'metric':{'name':'benchmark.memory.peak','unit':'By','value':after},
        'baseline_rss':{'unit':'By','value':before},
        'operations':{'name':'benchmark.operations','unit':'{operation}','value':1},
        'work_counters':getattr(operation,'last_stats',None),
        'propagation':getattr(operation,'last_metrics',None),
        'worker_pid':os.getpid()},sort_keys=True))

if __name__=='__main__':main()
