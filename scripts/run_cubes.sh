#!/bin/zsh
# Cube and conquer para el certificado ártico de C_2: 9 casos según M_0[0][0], M_1[0][0] ∈ {1,2,3},
# hasta P en paralelo, con ruptura de simetría y tope de tiempo por caso. Guardián de memoria: corta todo
# si la memoria libre baja de 12 %. Uso: scripts/run_cubes.sh d B P segundos
cd "$(dirname "$0")/.."
d=$1; B=$2; P=$3; LIM=$4
OUT=.sat_runs/d${d}_B${B}_$(date +%Y%m%d_%H%M); mkdir -p $OUT
cubes=(); for v0 in $(seq 1 $B); do for v1 in $(seq 1 $B); do cubes+=("$v0 $v1"); done; done
printf '%s\n' "${cubes[@]}" | xargs -P $P -L 1 zsh -c '
  /usr/bin/time -l timeout '"$LIM"' python3 -c "import sys; sys.path.insert(0,\"scripts\"); from carry_srs_sat import main; main(2,'"$d"','"$B"',sym=True,cube={\"0\":$0,\"1\":$1})" > '"$OUT"'/cubo_$0_$1.log 2>&1
  echo "cubo ($0,$1) exit=$?" >> '"$OUT"'/resumen.txt' &
XP=$!
minfree=100
while kill -0 $XP 2>/dev/null; do
  f=$(memory_pressure -Q | awk '/free percentage/{gsub("%","",$5); print $5}')
  [ -n "$f" ] && [ "$f" -lt "$minfree" ] && minfree=$f && echo "$minfree" > $OUT/memoria_libre_minima.txt
  if [ -n "$f" ] && [ "$f" -lt 12 ]; then echo "GUARDIAN: memoria libre $f% -> corto todo" >> $OUT/resumen.txt; pkill -f "carry_srs_sat import main"; break; fi
  grep -l "ártico.*: SAT " $OUT/cubo_*.log(N) >/dev/null 2>&1 && { echo "SAT encontrado -> corto el resto" >> $OUT/resumen.txt; pkill -f "carry_srs_sat import main"; break; }
  sleep 10
done
wait
echo "FIN $(date) | memoria libre mínima: $minfree%" >> $OUT/resumen.txt
echo $OUT
