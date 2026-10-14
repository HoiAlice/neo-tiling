for sh in 16,8 8,16 20,4 4,20 24,0 0,24; do
  export WS_DX=${sh%,*} WS_DY=${sh#*,}
  /Users/olegoleg/Code/neo-tiling/.venv/bin/python ws_free.py 2>&1 | grep -v Warn | tail -2
  WS_VAR=gd:0.002:12 WS_N=12 /Users/olegoleg/Code/neo-tiling/.venv/bin/python ws_fix.py 2>&1 | grep -v Warn
done
