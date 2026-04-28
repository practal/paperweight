import { configureDebugging, runTests } from "things";
import "./kernel/test.js";
import "./workbench.test.js";
import "./classical-define-with.test.js";

configureDebugging(console.log);
runTests();
