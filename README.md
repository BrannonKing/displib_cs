# displib_cs

Download the input files from https://displib.github.io/.

win_rt works and requires Gurobi. It's probably what you're looking for. It uses lazy constraints to avoid using too much memory.

disjunct_cp also works using ORTools' SAT solver. It will use a lot of memory on the larger inputs. If you really want to solve a large problem, get a beefy machine and crank up the threads and time on this project.
