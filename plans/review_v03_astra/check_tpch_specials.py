from pathlib import Path
import importlib.util
import polars as pl
root=Path(__file__).resolve().parents[2]
s=importlib.util.spec_from_file_location('tpch_check',root/'bench/tpch/run_polars.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for got,want in [(0.0,float('inf')),(-float('inf'),float('inf')),(float('inf'),float('inf')),(float('nan'),float('nan'))]:
 print(repr(got),repr(want),'->',repr(m.same(pl.DataFrame({'x':[got]}),pl.DataFrame({'x':[want]}))))
