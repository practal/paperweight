import { beginTheory, declare, endTheory, exportTeX, print, setTeXMode } from "../workbench.js";

beginTheory();
declare("exists (x. P[x])");
declare("for-all (x. P[x])");
declare("for-all (x y. P[x, y])");
declare("less x y");
declare("implies x y");
declare("and x y");
declare("choose (x. P[x])");
declare("nat-sum n m (i. F[i])");
declare("function domain (x. F[x])");
declare("mul x y");
declare("real-numbers");
declare("equals x y");

//setTeXMode(true);
print("exists (x. P[x])");
print("for-all (x y. implies (less x y) P[x, y])"); 
print("choose (x. P[x])");
print("nat-sum n m (i. F[i])");
print("equals f (function real-numbers (x. mul x x))"); 
print("x y. implies (less x y) (exists (z. and (less x z) (less z y)))"); 

endTheory("Example-6");
