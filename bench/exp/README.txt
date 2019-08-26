This directory contains the 136 benchmark problems used in the experiments in our APLAS 2019 paper.

They are obtained from benchmark sets for TravMC2 [1], HorSat2 [2], and HorSatP [3] via the translation of Kobayashi et al.'s POPL 2017 paper [4].
The source of each file is written at the top of the file as a comment.

Note that the HORS model checking problems written in HORS + CASE format are not included because they cannot be converted into HFL model checking problems by the translator we used (its implementation is rather naive).
Some files that HorSatP emits error while processing are also excluded.

References:
[1] Robin P. Neatherway and C.-H. Luke Ong. TravMC2: Higher-order model checking for alternating parity tree automata. In proceedings of the 2014 International SPIN Symposium on Model Checking of Software (SPIN 2014). pp. 129-132. ACM (2014)
[2] Naoki Kobayashi. HorSat2: A model checker for HORS based on SATuration. https://github.com/hopv/horsat2 (2015)
[3] Ryota Suzuki, Koichi Fujima, Naoki Kobayashi, and Takeshi Tsukada. Streett automata model checking of higher-order recursion schemes. In proceedings of the 2nd International Conference on Formal Structures for Computation and Deduction (FSCD 2017). LIPIcs, vol. 84, pp. 32:1-32:18. Schloss Dagstuhl-Leibniz-Zentrum fuer Informatik (2017)
[4] Naoki Kobayashi, Étienne Lozes, and Florian Bruse. On the relationship between higher-order recursion schemes and higher-order fixpoint logic. In proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages (POPL 2017). pp. 246-259. ACM (2017)
