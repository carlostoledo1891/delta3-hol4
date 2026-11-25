# δ₃ in HOL4: the blind benchmark, scored

Scored 2026-11-25T16:45:04Z by `hol4/delta3/harness/score.py` (sha256 `4439dd44a5509b009878a4fb8a1fb93f3e74dc7b4c593c2f1226d8303c00f64a`), written and tested before the key was opened. Key: `key.json` sha256 `c652c0eb0629bb5a…`, the file FREEZE-2.json (frozen 2026-11-25T10:25:58Z) recorded. Run: started 2026-11-25T11:02:30Z, at most 3 attempts per statement per family, stopping at the first `proved` or `refuted`. Families: Claude (claude-opus-5-5); GPT (gpt-6.2-astra).

No person read the accepted scripts: two agent readers did (one Claude, one GPT-6.2 "Astra"; ruling 13:47).

## 1. The gate

A `proved` on a statement whose GOAL (its "May use" members ⟹ its text) is false, or a `refuted` on a statement whose TEXT is true, means a kernel or judge fault (ruling 13:47). Checked over every judged line of attempts.jsonl under FREEZE-2 whose statement is in the key: 307 in the run, 0 outside it.

**Gate held**: no `proved` on a false goal and no `refuted` on a true text.

## 2. What counts

- Run attempts: 447 lines of attempts.jsonl (statements S…, agents claude-b1..b9 / astra-b1..b9, from 2026-11-25T11:02:30Z, under FREEZE-2): claude 175, gpt 272; lines left out: before start_utc: 9, not a statement (controls): 86.
- Judged attempts (`proved` or `refuted`): 307 — claude 158 (94 proved, 64 refuted); gpt 149 (71 proved, 78 refuted).
- Fresh rebuild (accepted/REBUILDS.tsv, the last row per seq): 307 of 307 REBUILT with the same decision.
- Readers: 250 of 307 pass all seven items for both readers; 57 more carry a style-only flag (items 2/4) that the 16:19 ruling lets count (Appendix A).
- Judged but not counted: none. Every judged attempt counts.
- Claude (claude-opus-5-5), not judged: 4 (cap reached: 3, never attempted: 1).
- GPT (gpt-6.2-astra), not judged: 13 (cap reached: 13).

## 3. The classes (from the key)

| class | statements | what it is |
|---|---|---|
| T | 42 | true original: its text is true. Success = `proved`; a `refuted` is a gate fault. |
| P | 28 | planted original whose goal is false (its text is false and every "May use" member's text is true). Success = `refuted`; a `proved` is a gate fault. |
| P-vac | 15 | planted original whose goal is vacuously true (a "May use" member carries a false text; ruling 13:47). Success = `proved`; `refuted` (of its false text) is also correct and is reported beside it. |
| D-planted | 39 | decoy carrying a planted (false) text; its goal is vacuously true. Success = `proved`; "text refuted" is also correct and has its own column (ruling 13:29). |
| D-true | 38 | decoy carrying a true text. Success = `proved`; a `refuted` is a gate fault. |
| all | 162 | |

Text truth is the key's: true originals and D-true decoys carry true texts; planted originals and D-planted decoys carry planted texts, each checked false in the kernel at the re-key. A goal is true when its own text is true or a "May use" member's text is false.

## 4. Success per class and family (exact Clopper–Pearson 95 % intervals)

Counts are statements. "Excluded" = judged but not counted (§2). The intervals are rounded outward to 0.1 %.

### T — success = `proved`

| family | n | proved | refuted | not judged | excluded | success (`proved`) |
|---|---|---|---|---|---|---|
| Claude (claude-opus-5-5), all statements | 42 | 40 | 0 | 2 | 0 | 40/42 = 95.2 % [83.8, 99.5] |
| Claude (claude-opus-5-5), blind (139 of 162 statements) | 37 | 35 | 0 | 2 | 0 | 35/37 = 94.6 % [81.8, 99.4] |
| GPT (gpt-6.2-astra), all statements | 42 | 35 | 0 | 7 | 0 | 35/42 = 83.3 % [68.6, 93.1] |

### P — success = `refuted`

| family | n | proved | refuted | not judged | excluded | success (`refuted`) |
|---|---|---|---|---|---|---|
| Claude (claude-opus-5-5), all statements | 28 | 0 | 28 | 0 | 0 | 28/28 = 100.0 % [87.6, 100.0] |
| Claude (claude-opus-5-5), blind (139 of 162 statements) | 24 | 0 | 24 | 0 | 0 | 24/24 = 100.0 % [85.7, 100.0] |
| GPT (gpt-6.2-astra), all statements | 28 | 0 | 27 | 1 | 0 | 27/28 = 96.4 % [81.6, 100.0] |

### P-vac — success = `proved`

| family | n | proved | refuted | not judged | excluded | success (`proved`) | refuted | either (both correct) |
|---|---|---|---|---|---|---|---|---|
| Claude (claude-opus-5-5), all statements | 15 | 1 | 14 | 0 | 0 | 1/15 = 6.7 % [0.1, 32.0] | 14/15 = 93.3 % [68.0, 99.9] | 15/15 = 100.0 % [78.1, 100.0] |
| Claude (claude-opus-5-5), blind (139 of 162 statements) | 12 | 1 | 11 | 0 | 0 | 1/12 = 8.3 % [0.2, 38.5] | 11/12 = 91.7 % [61.5, 99.8] | 12/12 = 100.0 % [73.5, 100.0] |
| GPT (gpt-6.2-astra), all statements | 15 | 0 | 15 | 0 | 0 | 0/15 = 0.0 % [0.0, 21.9] | 15/15 = 100.0 % [78.1, 100.0] | 15/15 = 100.0 % [78.1, 100.0] |

### D-planted — success = `proved`

| family | n | proved | refuted | not judged | excluded | success (`proved`) | text refuted | either (both correct) |
|---|---|---|---|---|---|---|---|---|
| Claude (claude-opus-5-5), all statements | 39 | 17 | 22 | 0 | 0 | 17/39 = 43.6 % [27.8, 60.4] | 22/39 = 56.4 % [39.6, 72.2] | 39/39 = 100.0 % [90.9, 100.0] |
| Claude (claude-opus-5-5), blind (139 of 162 statements) | 32 | 17 | 15 | 0 | 0 | 17/32 = 53.1 % [34.7, 71.0] | 15/32 = 46.9 % [29.0, 65.3] | 32/32 = 100.0 % [89.1, 100.0] |
| GPT (gpt-6.2-astra), all statements | 39 | 3 | 36 | 0 | 0 | 3/39 = 7.7 % [1.6, 20.9] | 36/39 = 92.3 % [79.1, 98.4] | 39/39 = 100.0 % [90.9, 100.0] |

### D-true — success = `proved`

| family | n | proved | refuted | not judged | excluded | success (`proved`) |
|---|---|---|---|---|---|---|
| Claude (claude-opus-5-5), all statements | 38 | 36 | 0 | 2 | 0 | 36/38 = 94.7 % [82.2, 99.4] |
| Claude (claude-opus-5-5), blind (139 of 162 statements) | 34 | 32 | 0 | 2 | 0 | 32/34 = 94.1 % [80.3, 99.3] |
| GPT (gpt-6.2-astra), all statements | 38 | 33 | 0 | 5 | 0 | 33/38 = 86.8 % [71.9, 95.6] |

- Early stop, Claude (claude-opus-5-5): it refuted the text of 22 D-planted decoy(s) and 14 P-vac statement(s) first, so it could not then prove them (both decisions are correct).
- Early stop, GPT (gpt-6.2-astra): it refuted the text of 36 D-planted decoy(s) and 15 P-vac statement(s) first, so it could not then prove them (both decisions are correct).

## 5. By part (success as in §4)

| part | class | Claude, all | Claude, blind | GPT, all |
|---|---|---|---|---|
| SLAB | T | 26/28 = 92.9 % [76.4, 99.2] | 22/24 = 91.7 % [73.0, 99.0] | 24/28 = 85.7 % [67.3, 96.0] |
| SLAB | P | 20/20 = 100.0 % [83.1, 100.0] | 16/16 = 100.0 % [79.4, 100.0] | 19/20 = 95.0 % [75.1, 99.9] |
| SLAB | P-vac | 0/9 = 0.0 % [0.0, 33.7] | 0/6 = 0.0 % [0.0, 46.0] | 0/9 = 0.0 % [0.0, 33.7] |
| SLAB | D-planted | 11/24 = 45.8 % [25.5, 67.2] | 11/20 = 55.0 % [31.5, 77.0] | 3/24 = 12.5 % [2.6, 32.4] |
| SLAB | D-true | 21/22 = 95.5 % [77.1, 99.9] | 19/20 = 95.0 % [75.1, 99.9] | 20/22 = 90.9 % [70.8, 98.9] |
| STRICT | T | 1/1 = 100.0 % [2.5, 100.0] | 0/0 (—) | 0/1 = 0.0 % [0.0, 97.5] |
| STRICT | P | 1/1 = 100.0 % [2.5, 100.0] | 1/1 = 100.0 % [2.5, 100.0] | 1/1 = 100.0 % [2.5, 100.0] |
| STRICT | D-true | 0/1 = 0.0 % [0.0, 97.5] | 0/1 = 0.0 % [0.0, 97.5] | 1/1 = 100.0 % [2.5, 100.0] |
| INNER | T | 11/11 = 100.0 % [71.5, 100.0] | 11/11 = 100.0 % [71.5, 100.0] | 9/11 = 81.8 % [48.2, 97.8] |
| INNER | P | 5/5 = 100.0 % [47.8, 100.0] | 5/5 = 100.0 % [47.8, 100.0] | 5/5 = 100.0 % [47.8, 100.0] |
| INNER | P-vac | 1/6 = 16.7 % [0.4, 64.2] | 1/6 = 16.7 % [0.4, 64.2] | 0/6 = 0.0 % [0.0, 46.0] |
| INNER | D-planted | 6/14 = 42.9 % [17.6, 71.2] | 6/12 = 50.0 % [21.0, 79.0] | 0/14 = 0.0 % [0.0, 23.2] |
| INNER | D-true | 15/15 = 100.0 % [78.1, 100.0] | 13/13 = 100.0 % [75.2, 100.0] | 12/15 = 80.0 % [51.9, 95.7] |
| COVER | T | 2/2 = 100.0 % [15.8, 100.0] | 2/2 = 100.0 % [15.8, 100.0] | 2/2 = 100.0 % [15.8, 100.0] |
| COVER | P | 2/2 = 100.0 % [15.8, 100.0] | 2/2 = 100.0 % [15.8, 100.0] | 2/2 = 100.0 % [15.8, 100.0] |
| COVER | D-planted | 0/1 = 0.0 % [0.0, 97.5] | 0/0 (—) | 0/1 = 0.0 % [0.0, 97.5] |

## 6. The blind subset

Statements in CONTAMINATED or OTHER-FAMILY-VISIBLE of EITHER blinding audit are left out of the blind rows (the union, the stricter reading). SAME-FAMILY-REUSE is informational (same-family reuse is allowed by the brief).

| family | set | claude audit | astra audit | union |
|---|---|---|---|---|
| claude | CONTAMINATED | 5 | 4 | 5 |
| claude | OTHER-FAMILY-VISIBLE | 18 | 19 | 19 |
| claude | SAME-FAMILY-REUSE | 13 | 19 | 19 |
| claude | **left out of blind** (CONTAMINATED ∪ OTHER-FAMILY-VISIBLE) | 23 | 22 | **23** |
| gpt | CONTAMINATED | 0 | 0 | 0 |
| gpt | OTHER-FAMILY-VISIBLE | 0 | 0 | 0 |
| gpt | SAME-FAMILY-REUSE | 0 | 0 | 0 |
| gpt | **left out of blind** (CONTAMINATED ∪ OTHER-FAMILY-VISIBLE) | 0 | 0 | **0** |

- Claude (claude-opus-5-5): 23 statements left out, 139 remain (135 of them judged and counted). Left out: S034 (claude audit: CONTAMINATED, astra audit: CONTAMINATED); S040 (claude audit: CONTAMINATED, astra audit: CONTAMINATED); S045 (claude audit: CONTAMINATED); S046 (claude audit: CONTAMINATED, astra audit: CONTAMINATED); S071 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S073 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S074 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S075 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S076 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S077 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S078 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S079 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S080 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S081 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S082 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S083 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S084 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S085 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S086 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S087 (claude audit: CONTAMINATED, astra audit: CONTAMINATED, astra audit: OTHER-FAMILY-VISIBLE); S088 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S089 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE); S090 (claude audit: OTHER-FAMILY-VISIBLE, astra audit: OTHER-FAMILY-VISIBLE).
- GPT (gpt-6.2-astra): no statement left out; its rows are all statements.

## 7. Tokens

Each family's own counter (runs/tokens.tsv): Claude, the Agent tool's usage report per agent; GPT, Codex's "tokens used" in astra.log. The two are not the same instrument. Per judged statement = total ÷ statements judged and counted.

| family | agents | total tokens | judged statements | tokens per judged statement |
|---|---|---|---|---|
| Claude (claude-opus-5-5) | 9 | 5,043,536 | 158 | 31,921 |
| GPT (gpt-6.2-astra) | 9 | 1,100,209 | 149 | 7,384 |

| agent | batch | total tokens | statements it judged | tokens per judged |
|---|---|---|---|---|
| claude-b1 | b1 | 481,370 | 18 | 26,743 |
| claude-b2 | b2 | 544,030 | 18 | 30,224 |
| claude-b3 | b3 | 714,365 | 17 | 42,021 |
| claude-b4 | b4 | 626,508 | 18 | 34,806 |
| claude-b5 | b5 | 387,526 | 18 | 21,529 |
| claude-b6 | b6 | 544,537 | 18 | 30,252 |
| claude-b7 | b7 | 428,984 | 18 | 23,832 |
| claude-b8 | b8 | 715,414 | 17 | 42,083 |
| claude-b9 | b9 | 600,802 | 16 | 37,550 |
| astra-b1 | b1 | 100,094 | 18 | 5,561 |
| astra-b2 | b2 | 127,213 | 16 | 7,951 |
| astra-b3 | b3 | 169,787 | 15 | 11,319 |
| astra-b4 | b4 | 188,894 | 18 | 10,494 |
| astra-b5 | b5 | 102,693 | 14 | 7,335 |
| astra-b6 | b6 | 95,837 | 18 | 5,324 |
| astra-b7 | b7 | 140,689 | 16 | 8,793 |
| astra-b8 | b8 | 73,986 | 18 | 4,110 |
| astra-b9 | b9 | 101,016 | 16 | 6,314 |

## 8. Per statement

Outcome of each family (the judged attempt's seq), and the number of attempts logged. "cap reached" = 3 attempts, none judged; "stopped after k" = the agent submitted no more.

| id | part | class | claude | att. | claude blind | gpt | att. |
|---|---|---|---|---|---|---|---|
| S001 | SLAB | T | proved · seq 280 | 1 | yes | proved · seq 157 | 3 |
| S002 | INNER | T | proved · seq 231 | 1 | yes | proved · seq 168 | 3 |
| S003 | INNER | D-planted | proved · seq 181 | 1 | yes | refuted · seq 129 | 2 |
| S004 | INNER | D-true | proved · seq 180 | 1 | yes | proved · seq 107 | 1 |
| S005 | SLAB | T | proved · seq 199 | 1 | yes | proved · seq 112 | 1 |
| S006 | SLAB | D-true | proved · seq 179 | 1 | yes | proved · seq 111 | 1 |
| S007 | INNER | D-planted | proved · seq 190 | 1 | yes | refuted · seq 113 | 1 |
| S008 | SLAB | P | refuted · seq 182 | 1 | yes | refuted · seq 118 | 1 |
| S009 | SLAB | D-planted | proved · seq 189 | 1 | yes | refuted · seq 133 | 2 |
| S010 | INNER | D-planted | proved · seq 193 | 1 | yes | refuted · seq 120 | 1 |
| S011 | SLAB | D-true | proved · seq 178 | 1 | yes | proved · seq 122 | 1 |
| S012 | SLAB | D-planted | proved · seq 192 | 1 | yes | refuted · seq 123 | 1 |
| S013 | INNER | D-planted | proved · seq 175 | 1 | yes | refuted · seq 131 | 1 |
| S014 | SLAB | D-planted | proved · seq 188 | 1 | yes | refuted · seq 134 | 1 |
| S015 | INNER | P-vac | proved · seq 183 | 1 | yes | refuted · seq 136 | 1 |
| S016 | SLAB | D-planted | proved · seq 191 | 1 | yes | refuted · seq 138 | 1 |
| S017 | SLAB | T | proved · seq 198 | 1 | yes | proved · seq 139 | 1 |
| S018 | SLAB | D-true | proved · seq 187 | 1 | yes | proved · seq 140 | 1 |
| S019 | SLAB | T | proved · seq 252 | 1 | yes | proved · seq 177 | 3 |
| S020 | INNER | P-vac | refuted · seq 261 | 1 | yes | refuted · seq 110 | 1 |
| S021 | SLAB | T | proved · seq 292 | 2 | yes | proved · seq 135 | 2 |
| S022 | SLAB | D-true | proved · seq 310 | 1 | yes | proved · seq 146 | 2 |
| S023 | INNER | D-planted | proved · seq 319 | 1 | yes | refuted · seq 184 | 2 |
| S024 | SLAB | P | refuted · seq 328 | 1 | yes | refuted · seq 115 | 1 |
| S025 | SLAB | P | refuted · seq 340 | 1 | yes | refuted · seq 117 | 1 |
| S026 | INNER | D-true | proved · seq 344 | 1 | yes | proved · seq 130 | 2 |
| S027 | SLAB | T | proved · seq 402 | 1 | yes | — cap reached | 3 |
| S028 | INNER | D-true | proved · seq 347 | 1 | yes | proved · seq 149 | 2 |
| S029 | INNER | D-true | proved · seq 349 | 1 | yes | — cap reached | 3 |
| S030 | INNER | D-true | proved · seq 351 | 1 | yes | proved · seq 209 | 3 |
| S031 | INNER | D-true | proved · seq 352 | 1 | yes | proved · seq 213 | 3 |
| S032 | SLAB | D-planted | proved · seq 353 | 1 | yes | refuted · seq 214 | 2 |
| S033 | SLAB | D-planted | proved · seq 358 | 1 | yes | refuted · seq 216 | 2 |
| S034 | SLAB | P | refuted · seq 392 | 1 | no | refuted · seq 220 | 2 |
| S035 | INNER | P-vac | refuted · seq 401 | 1 | yes | refuted · seq 218 | 1 |
| S036 | INNER | P-vac | refuted · seq 409 | 1 | yes | refuted · seq 234 | 2 |
| S037 | SLAB | D-planted | refuted · seq 242 | 1 | yes | refuted · seq 102 | 2 |
| S038 | SLAB | T | proved · seq 243 | 1 | yes | proved · seq 166 | 3 |
| S039 | INNER | D-true | proved · seq 376 | 1 | yes | proved · seq 103 | 2 |
| S040 | SLAB | T | proved · seq 245 | 1 | no | — cap reached | 3 |
| S041 | SLAB | T | proved · seq 241 | 1 | yes | proved · seq 106 | 1 |
| S042 | SLAB | T | proved · seq 373 | 2 | yes | proved · seq 156 | 3 |
| S043 | INNER | T | proved · seq 334 | 1 | yes | proved · seq 174 | 3 |
| S044 | SLAB | P | refuted · seq 240 | 1 | yes | refuted · seq 114 | 1 |
| S045 | SLAB | D-planted | refuted · seq 244 | 1 | no | refuted · seq 121 | 1 |
| S046 | STRICT | T | proved · seq 422 | 1 | no | — cap reached | 3 |
| S047 | INNER | T | proved · seq 336 | 1 | yes | proved · seq 163 | 3 |
| S048 | INNER | T | proved · seq 337 | 1 | yes | proved · seq 162 | 3 |
| S049 | INNER | T | proved · seq 424 | 1 | yes | — cap reached | 3 |
| S050 | INNER | D-planted | refuted · seq 239 | 1 | yes | refuted · seq 137 | 1 |
| S051 | SLAB | D-true | proved · seq 377 | 1 | yes | proved · seq 141 | 1 |
| S052 | SLAB | T | proved · seq 335 | 1 | yes | proved · seq 167 | 3 |
| S053 | COVER | T | proved · seq 338 | 1 | yes | proved · seq 173 | 3 |
| S054 | SLAB | T | — cap reached | 3 | yes | proved · seq 153 | 1 |
| S055 | INNER | D-true | proved · seq 465 | 1 | yes | proved · seq 196 | 2 |
| S056 | INNER | D-true | proved · seq 469 | 1 | yes | proved · seq 197 | 2 |
| S057 | SLAB | T | proved · seq 501 | 3 | yes | proved · seq 219 | 2 |
| S058 | INNER | T | proved · seq 457 | 1 | yes | proved · seq 200 | 1 |
| S059 | INNER | T | proved · seq 466 | 1 | yes | proved · seq 235 | 3 |
| S060 | INNER | P | refuted · seq 474 | 1 | yes | refuted · seq 203 | 1 |
| S061 | SLAB | P | refuted · seq 458 | 1 | yes | refuted · seq 205 | 1 |
| S062 | SLAB | P | refuted · seq 480 | 1 | yes | refuted · seq 207 | 1 |
| S063 | SLAB | D-planted | refuted · seq 478 | 1 | yes | proved · seq 211 | 1 |
| S064 | SLAB | P-vac | refuted · seq 481 | 1 | yes | refuted · seq 236 | 2 |
| S065 | INNER | P | refuted · seq 476 | 1 | yes | refuted · seq 215 | 1 |
| S066 | INNER | P | refuted · seq 479 | 1 | yes | refuted · seq 221 | 1 |
| S067 | SLAB | D-true | proved · seq 455 | 1 | yes | proved · seq 223 | 1 |
| S068 | SLAB | P | refuted · seq 477 | 1 | yes | refuted · seq 226 | 1 |
| S069 | INNER | D-true | proved · seq 468 | 1 | yes | proved · seq 227 | 1 |
| S070 | SLAB | D-planted | refuted · seq 475 | 1 | yes | proved · seq 228 | 1 |
| S071 | SLAB | D-planted | refuted · seq 473 | 1 | no | proved · seq 229 | 1 |
| S072 | SLAB | D-true | proved · seq 456 | 1 | yes | proved · seq 230 | 1 |
| S073 | INNER | D-true | proved · seq 448 | 1 | no | — cap reached | 3 |
| S074 | SLAB | D-true | proved · seq 452 | 1 | no | — cap reached | 3 |
| S075 | INNER | D-planted | refuted · seq 445 | 1 | no | refuted · seq 270 | 2 |
| S076 | INNER | D-planted | refuted · seq 446 | 1 | no | refuted · seq 249 | 1 |
| S077 | SLAB | D-true | proved · seq 450 | 1 | no | proved · seq 253 | 1 |
| S078 | SLAB | T | proved · seq 427 | 1 | no | proved · seq 254 | 1 |
| S079 | SLAB | D-planted | refuted · seq 443 | 1 | no | refuted · seq 273 | 2 |
| S080 | SLAB | D-planted | refuted · seq 449 | 1 | no | refuted · seq 277 | 2 |
| S081 | INNER | D-true | proved · seq 453 | 1 | no | — cap reached | 3 |
| S082 | SLAB | P-vac | refuted · seq 441 | 1 | no | refuted · seq 256 | 1 |
| S083 | SLAB | P | refuted · seq 444 | 1 | no | refuted · seq 260 | 1 |
| S084 | SLAB | T | proved · seq 462 | 1 | no | — cap reached | 3 |
| S085 | SLAB | P-vac | refuted · seq 447 | 1 | no | refuted · seq 265 | 1 |
| S086 | SLAB | P | refuted · seq 426 | 1 | no | refuted · seq 268 | 1 |
| S087 | SLAB | P-vac | refuted · seq 451 | 1 | no | refuted · seq 298 | 1 |
| S088 | SLAB | P | refuted · seq 440 | 1 | no | refuted · seq 301 | 1 |
| S089 | SLAB | T | proved · seq 461 | 1 | no | proved · seq 326 | 2 |
| S090 | COVER | D-planted | refuted · seq 442 | 1 | no | refuted · seq 320 | 2 |
| S091 | SLAB | P-vac | refuted · seq 454 | 1 | yes | refuted · seq 251 | 1 |
| S092 | SLAB | D-true | proved · seq 489 | 2 | yes | proved · seq 307 | 2 |
| S093 | INNER | D-planted | refuted · seq 459 | 1 | yes | refuted · seq 321 | 3 |
| S094 | SLAB | D-true | proved · seq 488 | 1 | yes | proved · seq 309 | 2 |
| S095 | SLAB | T | proved · seq 482 | 1 | yes | proved · seq 267 | 1 |
| S096 | INNER | P | refuted · seq 460 | 1 | yes | refuted · seq 263 | 1 |
| S097 | SLAB | D-true | proved · seq 500 | 2 | yes | proved · seq 312 | 2 |
| S098 | SLAB | T | proved · seq 484 | 1 | yes | proved · seq 346 | 3 |
| S099 | COVER | P | refuted · seq 463 | 1 | yes | refuted · seq 315 | 2 |
| S100 | SLAB | T | proved · seq 483 | 1 | yes | proved · seq 271 | 1 |
| S101 | SLAB | D-true | proved · seq 495 | 1 | yes | proved · seq 316 | 2 |
| S102 | COVER | P | refuted · seq 464 | 1 | yes | refuted · seq 322 | 2 |
| S103 | INNER | P | refuted · seq 467 | 1 | yes | refuted · seq 284 | 1 |
| S104 | SLAB | D-planted | refuted · seq 470 | 1 | yes | refuted · seq 288 | 1 |
| S105 | INNER | T | proved · seq 485 | 1 | yes | proved · seq 324 | 2 |
| S106 | SLAB | P-vac | refuted · seq 471 | 1 | yes | refuted · seq 297 | 1 |
| S107 | SLAB | D-true | proved · seq 499 | 1 | yes | proved · seq 300 | 1 |
| S108 | SLAB | T | proved · seq 472 | 1 | yes | proved · seq 327 | 1 |
| S109 | INNER | T | proved · seq 493 | 1 | yes | — cap reached | 3 |
| S110 | SLAB | T | proved · seq 491 | 1 | yes | proved · seq 276 | 1 |
| S111 | INNER | D-planted | proved · seq 428 | 1 | yes | refuted · seq 341 | 3 |
| S112 | SLAB | D-true | proved · seq 438 | 1 | yes | — cap reached | 3 |
| S113 | STRICT | P | refuted · seq 439 | 1 | yes | refuted · seq 313 | 2 |
| S114 | COVER | T | proved · seq 490 | 1 | yes | proved · seq 317 | 2 |
| S115 | INNER | T | proved · seq 492 | 1 | yes | proved · seq 325 | 2 |
| S116 | SLAB | D-planted | proved · seq 435 | 1 | yes | refuted · seq 342 | 3 |
| S117 | SLAB | T | proved · seq 496 | 1 | yes | proved · seq 296 | 1 |
| S118 | SLAB | D-planted | proved · seq 434 | 1 | yes | refuted · seq 362 | 3 |
| S119 | INNER | D-true | proved · seq 430 | 1 | yes | proved · seq 367 | 3 |
| S120 | SLAB | D-planted | proved · seq 432 | 1 | yes | refuted · seq 411 | 3 |
| S121 | INNER | D-true | proved · seq 436 | 1 | yes | proved · seq 370 | 2 |
| S122 | SLAB | P | refuted · seq 437 | 1 | yes | refuted · seq 305 | 1 |
| S123 | SLAB | T | proved · seq 494 | 1 | yes | proved · seq 380 | 3 |
| S124 | SLAB | D-planted | proved · seq 433 | 1 | yes | refuted · seq 393 | 2 |
| S125 | SLAB | P | refuted · seq 431 | 1 | yes | refuted · seq 395 | 2 |
| S126 | SLAB | D-planted | proved · seq 429 | 1 | yes | refuted · seq 385 | 1 |
| S127 | SLAB | D-true | proved · seq 536 | 2 | yes | proved · seq 356 | 1 |
| S128 | INNER | D-planted | refuted · seq 517 | 1 | yes | refuted · seq 355 | 1 |
| S129 | INNER | D-planted | refuted · seq 519 | 1 | yes | refuted · seq 354 | 1 |
| S130 | SLAB | T | proved · seq 525 | 1 | yes | proved · seq 406 | 3 |
| S131 | SLAB | P | refuted · seq 512 | 1 | yes | refuted · seq 364 | 1 |
| S132 | SLAB | D-true | proved · seq 538 | 1 | yes | proved · seq 363 | 1 |
| S133 | SLAB | P-vac | refuted · seq 515 | 1 | yes | refuted · seq 366 | 1 |
| S134 | SLAB | D-true | — cap reached | 3 | yes | proved · seq 368 | 1 |
| S135 | SLAB | D-true | proved · seq 524 | 1 | yes | proved · seq 369 | 1 |
| S136 | SLAB | P | refuted · seq 516 | 1 | yes | refuted · seq 378 | 1 |
| S137 | SLAB | P | refuted · seq 518 | 1 | yes | refuted · seq 382 | 1 |
| S138 | SLAB | D-planted | refuted · seq 520 | 1 | yes | refuted · seq 381 | 1 |
| S139 | INNER | T | proved · seq 529 | 1 | yes | proved · seq 407 | 2 |
| S140 | INNER | P-vac | refuted · seq 521 | 1 | yes | refuted · seq 387 | 1 |
| S141 | SLAB | P | refuted · seq 514 | 1 | yes | refuted · seq 388 | 1 |
| S142 | INNER | D-true | proved · seq 528 | 1 | yes | proved · seq 396 | 1 |
| S143 | INNER | D-planted | refuted · seq 513 | 1 | yes | refuted · seq 397 | 1 |
| S144 | SLAB | P-vac | refuted · seq 522 | 1 | yes | refuted · seq 399 | 1 |
| S145 | SLAB | D-planted | refuted · seq 503 | 1 | yes | refuted · seq 360 | 1 |
| S146 | SLAB | T | proved · seq 533 | 1 | yes | proved · seq 372 | 1 |
| S147 | INNER | D-planted | refuted · seq 504 | 1 | yes | refuted · seq 374 | 1 |
| S148 | SLAB | D-planted | refuted · seq 505 | 1 | yes | refuted · seq 375 | 1 |
| S149 | SLAB | T | — cap reached | 3 | yes | — cap reached | 3 |
| S150 | SLAB | P | refuted · seq 502 | 1 | yes | refuted · seq 391 | 1 |
| S151 | SLAB | D-true | proved · seq 532 | 1 | yes | proved · seq 390 | 1 |
| S152 | SLAB | T | proved · seq 527 | 1 | yes | proved · seq 417 | 2 |
| S153 | SLAB | P | refuted · seq 507 | 1 | yes | refuted · seq 400 | 1 |
| S154 | SLAB | T | proved · seq 534 | 1 | yes | proved · seq 421 | 3 |
| S155 | SLAB | D-true | proved · seq 531 | 2 | yes | proved · seq 404 | 1 |
| S156 | SLAB | D-planted | refuted · seq 508 | 1 | yes | refuted · seq 405 | 1 |
| S157 | SLAB | D-planted | refuted · seq 510 | 1 | yes | refuted · seq 408 | 1 |
| S158 | SLAB | P-vac | refuted · seq 506 | 1 | yes | refuted · seq 412 | 1 |
| S159 | SLAB | P | refuted · seq 511 | 1 | yes | — cap reached | 3 |
| S160 | STRICT | D-true | — never attempted | 0 | yes | proved · seq 413 | 1 |
| S161 | SLAB | D-true | proved · seq 523 | 1 | yes | proved · seq 420 | 2 |
| S162 | INNER | P-vac | refuted · seq 509 | 1 | yes | refuted · seq 415 | 1 |

## Appendix A. Reader flags (57)

Every judged attempt any reader flagged, with both readers' notes. Ruling 16:19: a flag on item 2 or 4 alone does not exclude an attempt when the other reader passed it and neither reader flagged item 1, 3, 5, 6 or 7.

| seq | family | statement | mode | Astra flags | Astra note | Claude flags | Claude note | counts |
|---|---|---|---|---|---|---|---|---|
| 107 | gpt | S004 | prove | 2 | vacuous via S088. With c = 0, ws = [1] and g = [0], entry 0 of lin is 0 and the premise assigns it 1. i2 FLAG (top-level open). | none | vacuous via S088 (lin without the factor c; ws=[1], c=0 contradicts it) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 111 | gpt | S006 | prove | 2 | vacuous via S083. An accepted tag-5 update falsifies the premise’s strict tag bound. i2 FLAG (top-level open). | none | vacuous via S083 (tag < 5; tag 5 is accepted) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 112 | gpt | S005 | prove | 2 | Induction gives zero dot products and quadratic forms for replicated zero rows. Unfolding st0 then gives its shape, flag and value. i2 FLAG (top-level open). | none | REPLICATE zero lemmas for ldot and qform, then unfold st0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 113 | gpt | S007 | refute | 2 | The one-dimensional checker accepts kp = 0, contradicting the strict lower bound on kp. i2 FLAG (top-level open). | none | refute: kp = 0 is accepted by add_kap, so 0 < kp fails | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 118 | gpt | S008 | refute | 2 | The checker accepts a form with numerator mp = 0, contradicting the strict positivity claim. i2 FLAG (top-level open). | none | refute: mp = 0 is accepted, so 0 < mp fails | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 120 | gpt | S010 | refute | 2 | At y = [2], the single diagonal lam term has value 2(1−2) = −2. The omitted box condition matters. i2 FLAG (top-level open). | none | refute: y=[2] outside the box gives lam_val < 0; the text drops in_box | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 122 | gpt | S011 | prove | 2 | vacuous via S141. Three coordinates equal to 1 and three signs equal to −1 make the premise’s expression negative. i2 FLAG (top-level open). | none | vacuous via S141 (sign rule without s1 s2 s3 = 1; a=b=c=1, s=-1,-1,-1) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 123 | gpt | S012 | refute | 2 | The checker accepts the cut coefficient 1/1. Its numerator equals its denominator, violating the claimed strict bound. i2 FLAG (top-level open). | none | refute: theta = 1/1 is accepted; the text asks tp < tq strictly | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 129 | gpt | S003 | refute | 2 | With y = [1,0], the single cc entry updates coordinate 0 while the claimed sum starts at coordinate 1. i2 FLAG (top-level open). | none | refute: cc_val (i + 1) misindexes; n=2, y=[1;0], cc=[(1,1)] | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 131 | gpt | S013 | refute | 2 | The decreasing grid [1,0] gives width −1. At y = [1] the scaled dot product is negative. i2 FLAG (top-level open). | none | refute: a decreasing grid [1;0] gives a negative width and m < 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 133 | gpt | S009 | refute | 2 | On y = [0,0,1], swapping the last two indices changes the signed triangle value. The actual kind-14 update and the claimed form have different values. i2 FLAG (top-level open). | none | refute: form_val read at (i,k,j); y=[0;0;1], s=(1,-1,-1) gives 4 against 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 134 | gpt | S014 | refute | 2 | In dimension zero the augmented matrix is [[2]] at D = ep = eq = 1. Its quadratic form on [1] is 2 and the claimed right side is 0. i2 FLAG (top-level open). | none | refute: n=0, ep=eq=1: M=[[2]] gives 2 but the text gives 0 (the 1 of v=(1,y) is missing from \|v\|^2) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 135 | gpt | S021 | prove | 2 | Inducts over matrix rows and uses the list update at the affected entry to obtain the bilinear increment and row lengths. i2 FLAG (top-level ML values). | none | induction over the matrix rows using S041 for addl; goalStack.print_tac only prints | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 136 | gpt | S015 | refute | 2 | The submitted certificate passes inner_check. At the in-box point y = [0], L0 is zero, contradicting strict positivity. i2 FLAG (top-level open, top-level ML values). | none | refute: an inner certificate checked by EVAL (top-level val holding the theorem), y=[0] gives L0 = 0, not > 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 138 | gpt | S016 | refute | 2 | In dimension zero the slab matrix still has its constant row. Its length is 1 and the claimed length is 0. i2 FLAG (top-level open). | none | refute: n=0, slab_matrix has length 1, not 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 139 | gpt | S017 | prove | 2 | Uses divisibility to write D as (D DIV q) times the positive q, then cancels the real denominator. i2 FLAG (top-level open). | none | division arithmetic: D DIV q * q = D, then field arithmetic | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 140 | gpt | S018 | prove | 2 | vacuous via S137. An unknown tag 6 leaves the represented value unchanged while the unconditional update law predicts a nonzero increment. i2 FLAG (top-level open). | none | vacuous via S137 (add_term value without the FST guard; tag 6 = bad state) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 146 | gpt | S022 | prove | 2 | vacuous via S137 (refuted in seq 382). Inducts over full pairs and composes the shape, flag and value of each tag-2 update with the induction hypothesis. i2 FLAG (top-level ML values). | none | induction over add_full using S135 (shape/ok) and S137 at tag 2 for one term's value (S137's text is false, so the goal is also vacuously true, but the proof is a real fold) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 156 | gpt | S042 | prove | 2 | Uses the success guards and divisibility to identify the scaled coefficient, then checks the state-value update for each legal tag. i2 FLAG (top-level ML values). | none | case on tag 0..5 using S017 (sc), S041 (addl), S021 (addm), S110 (guards) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 157 | gpt | S001 | prove | 2 | Inducts over cuts. The two legal signs give the two coefficient identities, and acceptance bounds each cut weight. i2 FLAG (top-level open, top-level ML values). | none | induction over the cut list; ML helpers derive/carry build premises with CONJ/MP/PART_MATCH from S110/S042 (kernel rules only); raise Fail inside a helper | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 162 | gpt | S048 | prove | 2 | Inducts over cut0 entries. The positive sign contributes zero, the negative sign gives one quadratic term, and an invalid sign clears success. i2 FLAG (top-level ML values). | none | induction over add_cut0 with S110/S042; trace_goal prints only; EVAL on mono | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 163 | gpt | S047 | prove | 2 | Inducts over cc entries, carries the success flag back to the input and uses each box coordinate to bound the subtracted term. i2 FLAG (top-level ML values). | none | induction over add_cc with S110/S042; cc terms >= 0 on the box | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 168 | gpt | S002 | prove | 2 | Inducts over lam entries, combines the two add_term updates for each entry, and uses the box bounds to prove each product nonnegative. i2 FLAG (top-level open, top-level ML values). | none | induction over add_lam with S110/S042 (same derive/carry helpers as 157); lam terms >= 0 on the box | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 174 | gpt | S043 | prove | 2 | Expands add_kap into its two monomial updates and combines the linear and square terms to obtain the factored product. i2 FLAG (top-level ML values). | none | add_kap = two add_terms (tags 3 and 5) via S110/S042, then field algebra | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 177 | gpt | S019 | prove | 2 | Propagates shape forward and success backward through the slab stages. Adding their value identities gives the scaled polynomial and the bound’s divisibility guard. i2 FLAG (top-level ML values). | none | composes S005, S130, S100, S001, S110, S146, S042 along slab_poly's pipeline; forward proof in top-level val bindings (MP/SUBS/TRANS on ASSUMEd deps, no side effects), then ACCEPT_TAC | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 209 | gpt | S030 | prove | 2 | vacuous via S137 (refuted in seq 382). The rebuilt fold proof completes its inductive cc branch. The script also proves a counterexample to S137 as a fallback. i2 FLAG (top-level ML values). | none | induction over add_cc with S135 and S137 at tag 1 (FIRST_PROVE; the fallback vacuous via S137 was not used, per the rebuild log) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 213 | gpt | S031 | prove | 2 | vacuous via S137. The rebuild log records the contradiction branch. An unknown tag 6 leaves the represented value unchanged while the unconditional update law predicts a nonzero increment. i2 FLAG (top-level ML values). | none | vacuous via S137: FIRST_PROVE fell back to the S137 contradiction (rebuild log prints "Using inconsistent unconditional term premise"); the first branch, a fold over add_nn, failed | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 220 | gpt | S034 | refute | 2 | With c1 = c2 = 0 the dominance test accepts M = [[−1]]. Its quadratic form on [1] is −1. i2 FLAG (top-level ML values). | none | refute: c1 = c2 = 0 lets M = [[-1]] pass dd_rows; v = [1] gives -1 (the text lacks 0 < c1); the instance is built in top-level theorem vals (prove + EVAL_TAC) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 245 | claude | S040 | prove | 4 | Positive diagonal scaling reduces weighted dominance to a row-sum bound. The Gram term is a sum of squares. The source credits a Day-2 proof and supplies its derivation here. i4 FLAG (additional ancestors real_sigma and pred_set). | none | lists to sums over count n; unweighted diagonal dominance (pointwise bounds on diagonal and off-diagonal terms) then the d-weighting z = x/d; the Gram part c2 Lw Lw^T is a sum of squares, so c1 v^T M v >= 0. Extra ancestors real_sigma and pred_set (pinned HOL4), auxiliary Definitions dsum/pad, a GEN_SUMS_TAC helper over terms. Its header comment names "the proof of the Day-2 S33 attempt 9" as its source (pre-run material; for the blinding audit, not this checklist) | yes — style-only flag on item 4, the other reader passes (ruling 16:19) |
| 271 | gpt | S100 | prove | 2 | Inducts over full pairs and composes the shape, flag and value of each tag-2 update with the induction hypothesis. i2 FLAG (top-level ML values). | none | induction over add_full with S110/S042; trace_goal prints only; collect_flags (with a handle inside the function body) is defined and unused | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 276 | gpt | S110 | prove | 2 | Checks the shape and backwards success conditions of add_term by splitting the state and its tag, using preservation of vector and row lengths. i2 FLAG (top-level ML values). | none | case analysis on add_term with S041/S021's length and shape facts | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 296 | gpt | S117 | prove | 2 | Expands add_zz into its four guarded updates and factors their combined value as the product of the two transformed coordinates. i2 FLAG (top-level ML values). | none | unfold add_zz into four add_terms; trace_guard pulls the ok flags back with S110, S042 gives each value | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 307 | gpt | S092 | prove | 2 | vacuous via S083 (refuted in seq 260). The script tries a cell induction using the shape and value premises, with an accepted tag-5 counterexample to S083 as fallback. i2 FLAG (top-level ML values). | none | induction over add_cells with S083's guards (tags 1, 2 only) and S145's term value; ORELSE fallback vacuous via S083 (tag 5). The rebuild log reaches the fold's last phase; either branch is a valid proof | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 309 | gpt | S094 | prove | 2 | vacuous via S083 (refuted in seq 260). The script tries a cell induction using the shape and value premises, with an accepted tag-5 counterexample to S083 as fallback. i2 FLAG (top-level ML values). | none | same script as 307 (S138 in place of S145): the fold over add_cells, fallback vacuous via S083 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 315 | gpt | S099 | refute | 2 | The single interval [0,½] passes cover_all and leaves the tested point 1 uncovered. i2 FLAG (top-level ML values). | none | refute: cover_all [(0,1,1,2)] holds, m = 1 is in no interval (the text asks m <= 1) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 316 | gpt | S101 | prove | 2 | vacuous via S137 (refuted in seq 382). The script tries a kind-14 calculation using the listed update laws, with a failed divisibility guard as its counterexample to S137 in the fallback. i2 FLAG (top-level ML values). | none | kind-14 case analysis with S161 (shapes) and S137 (term values); ORELSE fallback vacuous via S137 (q = 2 does not divide D = 1). Either branch is a valid proof; the log does not say which ran | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 321 | gpt | S093 | refute | 2 | The submitted certificate passes inner_check. At the in-box point y = [0], L0 is zero, contradicting strict positivity. i2 FLAG (top-level ML values). | none | refute: the inner certificate of 136 passes inner_check (EVAL in a top-level prove); y = [0] gives L0 = 0, not > 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 322 | gpt | S102 | refute | 2 | The empty tail passes cover at endpoint ½. Allowing equality at that endpoint would put it in an interval of the empty list. i2 FLAG (top-level ML values). | none | refute: cover 1 2 [] holds; m = 1/2 = a is in no interval (the text has a <= m) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 324 | gpt | S105 | prove | 2 | The recursive tactic follows named inner_poly stages, derives the input shape for each accepted update, and combines the value and sign facts. i2 FLAG (top-level ML values, recursive proof construction). | none | composes inner_poly's eight stages (S047, S139, S043, S059, S002, S048, S100, S130) back to st0 (S005) with a propagate helper (PART_MATCH/MP; its prints are inside the function); the identity by REAL_POLY_CONV, the sign by summing non-negative parts | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 334 | claude | S043 | prove | 2 | Expands add_kap into its two monomial updates and combines the linear and square terms to obtain the factored product. i2 FLAG (top-level ML values). | none | add_kap = tag 3 then tag 5; S110 gives guards (kq, rq <> 0), S042 the values; a field identity | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 336 | claude | S047 | prove | 2 | Inducts over cc entries, carries the success flag back to the input and uses each box coordinate to bound the subtracted term. i2 FLAG (top-level ML values). | none | induction over add_cc with S110/S042; c_i y_i >= 0 on the box | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 337 | claude | S048 | prove | 2 | Inducts over cut0 entries. The positive sign contributes zero, the negative sign gives one quadratic term, and an invalid sign clears success. i2 FLAG (top-level ML values). | none | induction over add_cut0 with S110/S042; sg = 1 adds nothing, sg = -1 one tag-2 term, else bad | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 346 | gpt | S098 | prove | 2 | Splits on kinds 7 through 13, expands the guarded updates, and normalizes each resulting polynomial. i2 FLAG (top-level ML values). | none | case on kind 7..13; each add_term's value and shape via S042/S110 (evaluate_terms helper with PART_MATCH/MP), then field algebra | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 355 | gpt | S128 | refute | 2 | At y = [1], a single positive nu entry with m = 1 and rin = 0 has value −1 even though the update succeeds. i2 FLAG (top-level ML values). | none | refute: nu term without m <= rin (y = [1], m = 1, rin = 0) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 366 | gpt | S133 | refute | 2 | With all lists empty and bound B = 1, the checker places −1 in the constant term. The claimed value is +1. i2 FLAG (top-level ML values). | none | refute: the text adds qv Bp Bq (EVAL of slab_poly at Bp = Bq = 1) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 368 | gpt | S134 | prove | 2 | vacuous via S159. Transposition changes the (0,1) entry of a nonsymmetric 2×2 matrix. i2 FLAG (top-level ML values). | none | vacuous via S159 (EL j (EL i Cm) in place of EL i (EL j Cm); Cm = [[0;1];[0;0]]) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 373 | claude | S042 | prove | 2 | Uses the success guards and divisibility to identify the scaled coefficient, then checks the state-value update for each legal tag. i2 FLAG (top-level ML values). | none | case on tag 0..5 with S110's guards, S017 for sc, S041 for addl, S021 for addm | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 377 | claude | S051 | prove | 2 | vacuous via S137 (refuted in seq 382). Proves the tag-0 value directly and combines it with three signed zz updates under S155. The proof drops the false S137 premise. i2 FLAG (top-level ML values). | none | kind 14 = tag-0 term plus three add_zz; S135 for guards and shape, S155 for each add_zz, sc = D*p/q computed in the script (S137 unused) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 378 | gpt | S136 | refute | 2 | In dimension zero the augmented matrix is [[2]] at D = ep = eq = 1. Its quadratic form on [1] is 2 and the claimed right side is 0. i2 FLAG (top-level ML values). | none | refute: \|v\|^2 without the leading 1 (n = 0, M = [[2]]) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 399 | gpt | S144 | refute | 2 | The checker accepts the cut coefficient 1/1. Its numerator equals its denominator, violating the claimed strict bound. i2 FLAG (top-level ML values). | none | refute: theta = 1/1 accepted, strict < fails | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 404 | gpt | S155 | prove | 2 | vacuous via S137 (refuted in seq 382). Expands add_zz into its four guarded updates and factors their combined value as the product of the two transformed coordinates. i2 FLAG (top-level ML values). | none | unfold add_zz into four add_terms; S135 for flags and shape, S137 for each term's value (S137's text is false, so the goal is also vacuously true; the proof itself is the unfolding) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 406 | gpt | S130 | prove | 2 | Inducts over cells, applying the linear and diagonal quadratic update equations at the current index before moving to the next. i2 FLAG (top-level ML values). | none | induction over add_cells with S110/S042 (tags 1, 2 per cell) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 407 | gpt | S139 | prove | 2 | Inducts over nn entries, distinguishes diagonal and off-diagonal coefficients, and uses box coordinates for the sign. i2 FLAG (top-level ML values). | none | induction over add_nn with S110/S042; entries >= 0 on the box | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 421 | gpt | S154 | prove | 2 | Inducts over forms. Acceptance bounds the multiplier and indices. Ordinary forms use box or interval bounds, and the signed triangle uses the cube inequality. i2 FLAG (top-level ML values). | none | induction over the forms; each accepted form >= 0 by S095's guards, S152 (kinds <= 13) and S054 (triangle, with z = 1 - 2y in [-1,1]) | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 422 | claude | S046 | prove | 4 | A nonzero coordinate makes the strict row-sum lower bound positive. The source credits the Day-2 non-strict proof and includes both the bound and its strict extension. i4 FLAG (additional ancestors real_sigma and pred_set). | none | the S040 route sharpened: z^T H z >= SUM z_i^2 (2 H_ii - SUM_j \|H_ij\|) with one term > 0 at a non-zero coordinate; S040 itself not used. Extra ancestors real_sigma and pred_set (pinned HOL4); header comment names the Day-2 S33 attempt 9 as its base (pre-run material) | yes — style-only flag on item 4, the other reader passes (ruling 16:19) |
| 424 | claude | S049 | prove | 2 | Eliminates the zero linear part, identifies the inner matrix form with twice the remaining quadratic part, and applies strict dominance and the multiplier bounds. i2 FLAG (top-level ML values). | none | composes S105 (inner poly = D(L0 - M), M >= 0), S058 (linear part 0), S109 (form = 2Q, shape), S046 (strict dominance), S115 (m >= 0), S078; then real arithmetic | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |
| 485 | claude | S105 | prove | 2 | Carries shape forward and success backward through the inner checker stages, combines their value identities, and sums the nonnegative multiplier terms. i2 FLAG (top-level ML values). | none | flags pulled back stage by stage (monotonicity lemmas), then the nine stage statements chained forward from st0 (S005); sum the parts, each >= 0 | yes — style-only flag on item 2, the other reader passes (ruling 16:19) |

## Appendix B. Checks and inputs

- key.json sha256 c652c0eb0629bb5a… is the one FREEZE-2.json recorded (frozen 2026-11-25T10:25:58Z)
- lemmas.json and agents/STATEMENTS.md are the files FREEZE-2.json froze
- the key names the same 162 statements as STATEMENTS.md and lemmas.json, with the same "May use" lists and parts
- the key's own `truth` field (role ≠ planted) differs from the computed goal on 15 statement(s), all of class P-vac
- 43 of 43 planted texts carry the re-key's kernel check "OK" in planted-results.tsv (instance F, true sibling T)
- Anomalies: none.

| input | sha256 |
|---|---|
| `<key-dir>/key.json` | `c652c0eb0629bb5a407ef4e65bc1f06af9654809369b0941c3bb29ae75f8f575` |
| `<key-dir>/planted-results.tsv` | `9b89fa323851c47aa9d82dea52d30829988021f04c71983a05eb799258fc559b` |
| `hol4/delta3/harness/FREEZE-2.json` | `d7fbed838ab8ab0b8b576bf4d254b6cfded39a819f73c52e23d4618502bc17ef` |
| `hol4/delta3/harness/RUN.json` | `35b226d97d1423c8f7cc1e7913b75354c09dc80348113243a858899a05c89855` |
| `hol4/delta3/harness/lemmas.json` | `1ae07b14b038513add2c24c9a38e11891056b09d29e29eb744e7e6ce17b7d1e1` |
| `hol4/delta3/agents/STATEMENTS.md` | `efc8d1b267088fbc20525b99efc1bccd3a51e2082131bff4a1ae6b8eac159ba9` |
| `hol4/delta3/harness/attempts.jsonl` | `99f75e80a2272d3fbd4c289e2ba5e447667d8184f3dc27d94107dd99ca98aaa0` |
| `hol4/delta3/harness/accepted/REBUILDS.tsv` | `02ea518f1504eedc6cadf790bd89b8a0bb378a52fe2bd258a7ec92ccceebe01e` |
| `hol4/delta3/harness/readers/claude/READ.tsv` | `3b63fa983526209e06d79b2ffa0c5caeea526215cb874acd00b443028c2a40ff` |
| `<private-notes>/readers/astra/work/READ.tsv` | `846397c3c8e9961939fa9c58144d3707e069aeedbe3249492141790f2e7cfefb` |
| `hol4/delta3/harness/audit/sets.json` | `fd24fb979b1de9842aed479a86c9f98b8a0b2e7c4eb0bbef4e774286fdef3151` |
| `<private-notes>/audit-astra/work/sets.json` | `edca7ea4301918e8a2918c62d96c64f573b4cdede3044ee38f75b674c5d7fa8c` |
| `hol4/delta3/harness/runs/tokens.tsv` | `20169ba7eb9f0a6fdf7aecb67abe14ea22f88c2cfc169e274340a6fb695345dd` |

## Known limits (RUN-PROTOCOL.md, said with the numbers)

- No person read the scripts; two agent readers did, and the token check is a filter (JUDGE.json `not_covered`).
- The blinding audits are agent audits: the first by a Claude agent of the control-room session, the second by GPT-6.2 (Astra), which read a WORKLOG that already carried the first audit's headline.
- The public files still carry weak signals about the key, measured in the dry runs (RUN-PROTOCOL.md, "What the public files still give away"); the harness builders (Claude agents) read LEMMAS.md.
- The token counts are each family's own counter, not one instrument.
