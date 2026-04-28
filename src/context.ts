import { nat, RedBlackMap } from "things";
import { AbsSigSpec, addSubst, Binder, displayAbsSigSpec, emptyTheory, newSubst, parseDeclaration, parseTerm, Rule, Subst, Terms, Theorem, Theory, validateTerm } from "./kernel/index.js";
import { displayTermAsTeX } from "./kernel/tex.js";

export type TheoryLocalInfo<Id> = {
    declarations : AbsSigSpec<Id>[]
    axioms : Id[]
    definitions : Id[]
    theorems : Id[]
}

export class Context<Id, Term> {

    empty : Theory<Id, Term>
    currentTheory : Theory<Id, Term>
    theories : RedBlackMap<Id, Theory<Id, Term>>

    #localDeclarations : AbsSigSpec<Id>[] = []
    #localAxioms : Id[] = []
    #localDefinitions : Id[] = []
    #localTheorems : Id[] = []
    #theoryLocalInfo : Map<string, TheoryLocalInfo<Id>> = new Map()

    constructor(terms : Terms<Id, Term>,
        theories : RedBlackMap<Id, Theory<Id, Term>> = RedBlackMap(terms.ids))
    {
        this.empty = emptyTheory(terms);
        this.currentTheory = this.empty;
        this.theories = theories;
    }

    info() {
        console.log("");
        console.log("Theory has " + this.currentTheory.sig.size + " declarations and " +
            this.currentTheory.listAxioms().length + " axioms.");
        console.log("");
    }

    parse(term : string | Term) : Term | undefined {
        if (typeof term === "string")
            return parseTerm(this.currentTheory.sig, this.currentTheory.terms, term);
        else
            return term;
    }

    theory() : Theory<Id, Term> {
        return this.currentTheory;
    }

    beginTheory() {
        this.currentTheory = this.empty;
        this.#localDeclarations = [];
        this.#localAxioms = [];
        this.#localDefinitions = [];
        this.#localTheorems = [];
        console.log("Begin theory.");
    }

    reportError(error : string) : never {
        throw new Error(error);
    }

    importTheory(theoryName : string, allowAxioms : boolean) {
        const theoryId = this.currentTheory.terms.mkId(theoryName);
        const thy = this.theories.get(theoryId);
        if (thy === undefined)
            this.reportError("There is no theory '" + this.displayId(theoryId) + "' to import.");
        this.currentTheory = this.currentTheory.importTheory(thy, allowAxioms);
        const job = allowAxioms ? "Included" : "Used";
        console.log(job + " theory '" + this.displayId(theoryId) + "'.");
    }

    displayId(id : Id) : string {
        return this.currentTheory.terms.ids.display(id);
    }

    endTheory(theoryName : string) {
        const theoryId = this.currentTheory.terms.mkId(theoryName);
        if (this.theories.has(theoryId))
            this.reportError("There exists already a theory '" + this.displayId(theoryId) + "'.");
        this.theories = this.theories.set(theoryId, this.currentTheory);
        this.#theoryLocalInfo.set(theoryName, {
            declarations: [...this.#localDeclarations],
            axioms: [...this.#localAxioms],
            definitions: [...this.#localDefinitions],
            theorems: [...this.#localTheorems]
        });
        function howMany(n : nat, what : string) : string {
            if (n === 1) return "1 " + what;
            else return n + " " + what + "s";
        }
        console.log("End theory as '" + this.displayId(theoryId) + "' (" +
            howMany(this.currentTheory.sig.size, "declaration") + ", " +
            howMany(this.currentTheory.listAxioms().length, "axiom") + ", " +
            howMany(this.currentTheory.listDefinitions().length, "definition") + ", " +
            howMany(this.currentTheory.listTheorems().length, "theorem") + ").");
        console.log("");
    }

    restore(theoryName : string) {
        const theoryId = this.currentTheory.terms.mkId(theoryName);
        const thy = this.theories.get(theoryId);
        if (thy === undefined)
            this.reportError("There is no theory '" + this.displayId(theoryId) + "'.");
        this.currentTheory = thy;
    }

    declare(declaration : string) {
        const spec = parseDeclaration(this.currentTheory.sig, this.currentTheory.terms, declaration);
        if (spec === undefined) {
            this.reportError("Could not parse declaration '" + declaration + "'.");
        } else {
            this.currentTheory = this.currentTheory.declare(spec);
            this.#localDeclarations.push(spec);
            console.log("Declared '" + displayAbsSigSpec(this.currentTheory.terms.ids, spec) + "'.");
        }
    }

    validate(term : string) {
        const t = this.parse(term);
        if (t === undefined) {
            this.reportError("Could not parse '" + term + "' for validation.");
        } else {
            validateTerm(this.currentTheory.sig, this.currentTheory.terms, t);
            console.log("Successfully validated '" + this.currentTheory.terms.display(t) + "'.");
        }
    }

    parseItems(error : (item : string) => string, items : string | string[]) : Term[] {
        const list = (typeof items === "string") ? [items] : items;
        const termList : Term[] = [];
        for (const item of list) {
            const t = this.parse(item);
            if (t === undefined) {
                this.reportError(error(item));
            }
            termList.push(t);
        }
        return termList;
    }

    display(term : Term) : string {
        return this.currentTheory.terms.display(term);
    }

    printRule(label : string, rule : Rule<Term>) {
        let len = 0;
        for (const prem of rule.premises) {
            len = Math.max(len, this.display(prem).length);
        }
        len = Math.max(len, this.display(rule.conclusion).length);
        let sep = "";
        for (let i = 0; i < len + 4; i++) sep += "-";
        console.log(label);
        for (const prem of rule.premises) {
            console.log("  |  " + this.display(prem));
        }
        console.log("  |" + sep);
        console.log("  |  " + this.display(rule.conclusion));
    }

    axiom(label : string,
        conclusion : string, premises : string[] = [])
    {
        const tConclusion = this.parse(conclusion);
        if (tConclusion === undefined)
            this.reportError("Could not parse conclusion '" + conclusion + "' of axiom.");
        const tPremises =
            this.parseItems(s => "Could not parse premise '" + s + "' of axiom.", premises);
        validateTerm(this.currentTheory.sig, this.currentTheory.terms, tConclusion);
        for (const premise of tPremises) {
            validateTerm(this.currentTheory.sig, this.currentTheory.terms, premise);
        }
        const rule = { premises : tPremises, conclusion : tConclusion };
        const labelId = this.currentTheory.terms.mkId(label);
        this.currentTheory = this.currentTheory.axiom(labelId, rule);
        this.#localAxioms.push(labelId);
        this.printRule("Axiom " + label + ":", this.currentTheory.theorem(labelId).proof.rule);
    }

    define(head : string, definiens : string)
    {
        const decl = parseDeclaration(this.currentTheory.sig, this.currentTheory.terms, head);
        if (decl === undefined) this.reportError("Cannot parse head '" + head + "' of definition.");
        const label = this.currentTheory.terms.ids.display(decl[0][0]) + "_def";
        this.defineWithAs(label, "x y. equals x y", head, definiens);
    }

    defineAs(label : string, head : string, definiens : string)
    {
        this.defineWithAs(label, "x y. equals x y", head, definiens);
    }

    defineWith(relation : string, head : string, definiens : string)
    {
        const decl = parseDeclaration(this.currentTheory.sig, this.currentTheory.terms, head);
        if (decl === undefined) this.reportError("Cannot parse head '" + head + "' of definition.");
        const label = this.currentTheory.terms.ids.display(decl[0][0]) + "_def";
        this.defineWithAs(label, relation, head, definiens);
    }

    defineWithAs(label : string, relation : string, head : string, definiens : string)
    {
        const decl = parseDeclaration(this.currentTheory.sig, this.currentTheory.terms, head);
        if (decl === undefined) this.reportError("Cannot parse head '" + head + "' of definition.");
        const labelId = this.currentTheory.terms.mkId(label);
        const relationT = parseTerm(this.currentTheory.sig, this.currentTheory.terms, relation);
        if (relationT === undefined) this.reportError("Cannot parse relation '" + relation + "' of definition.");
        const headTheory = this.currentTheory.declare(decl);
        const headT = parseTerm(headTheory.sig, headTheory.terms, head);
        if (headT === undefined) this.reportError("Cannot parse head '" + head + "' of definition.");
        const definiensT = parseTerm(this.currentTheory.sig, this.currentTheory.terms, definiens);
        if (definiensT === undefined) this.reportError("Cannot parse definiens '" + definiens + "' of definition.");
        const currentTheory = this.currentTheory.defineWith(labelId, relationT, headT, definiensT);
        this.#localDefinitions.push(labelId);
        this.printRule("Definition " + label + ":", currentTheory.theorem(labelId).proof.rule);
        this.currentTheory = currentTheory;
    }

    lemma(label : string, thm : Theorem<Id, Term>) {
        const labelId = this.currentTheory.terms.mkId(label);
        this.currentTheory = this.currentTheory.note(labelId, thm);
        this.#localTheorems.push(labelId);
        this.printRule("Theorem " + label + ":", thm.proof.rule);
    }

    have(label : string, conclusion : string, premises : string[], thm : Theorem<Id, Term>, ) {
        const tConclusion = this.parse(conclusion);
        if (tConclusion === undefined)
            this.reportError("Could not parse conclusion '" + conclusion + "' of have.");
        const tPremises =
            this.parseItems(s => "Could not parse premise '" + s + "' of have.", premises);
        const terms = thm.theory.terms;
        const rule = thm.proof.rule;
        if (!terms.equal(tConclusion, rule.conclusion)) 
            this.reportError("Different conclusion than expected in have, expected: '" + 
                terms.display(tConclusion) + "', found '" + terms.display(rule.conclusion) + "'.");
        const N = Math.max(tPremises.length, rule.premises.length);
        for (let i = 0; i < N; i++) {
            if (tPremises[i] === undefined || rule.premises[i] === undefined) { 
                let message = "Different number of premises than expected in have, expected " + 
                    tPremises.length + " premises, but found " + rule.premises.length + " premise(s): ";
                for (let j = i; j < N; j++) {
                    const expected = tPremises[j] === undefined ? "none" : "'" + terms.display(tPremises[j]) + "'";
                    const found = rule.premises[j] === undefined ? "none" : "'" + terms.display(rule.premises[j]) + "'";
                    message += "\n    Premise " + j + ": expected " + expected + ", found: " + found;
                }      
                this.reportError(message);          
            }
            if (!terms.equal(tPremises[i], rule.premises[i])) 
                this.reportError("Different premise " + i + " than expected in have, expected: '" + 
                    terms.display(tPremises[i]) + "', found: '" + terms.display(rule.premises[i]) + "'.");
        }
        this.lemma(label, thm);
    }    
    
    note(conclusion : string, premises : string[], thm : Theorem<Id, Term>) : Theorem<Id, Term> {
       const tPremises =
            this.parseItems(s => "Could not parse premise '" + s + "' of note.", premises);
        const tConclusion = this.parse(conclusion);
        if (tConclusion === undefined)
            this.reportError("Could not parse conclusion '" + conclusion + "' of note.");
        const terms = thm.theory.terms;
        const rule = thm.proof.rule;
        if (!terms.equal(tConclusion, rule.conclusion)) 
            this.reportError("Different conclusion than expected in note, expected: '" + 
                terms.display(tConclusion) + "', found '" + terms.display(rule.conclusion) + "'.");
        const N = Math.max(tPremises.length, rule.premises.length);
        for (let i = 0; i < N; i++) {
            if (tPremises[i] === undefined || rule.premises[i] === undefined) { 
                let message = "Different number of premises than expected in have, expected " + 
                    tPremises.length + " premises, but found " + rule.premises.length + " premise(s): ";
                for (let j = i; j < N; j++) {
                    const expected = tPremises[j] === undefined ? "none" : "'" + terms.display(tPremises[j]) + "'";
                    const found = rule.premises[j] === undefined ? "none" : "'" + terms.display(rule.premises[j]) + "'";
                    message += "\n    Premise " + j + ": expected " + expected + ", found: " + found;
                }      
                this.reportError(message);          
            }
            if (!terms.equal(tPremises[i], rule.premises[i])) 
                this.reportError("Different premise " + i + " than expected in have, expected: '" + 
                    terms.display(tPremises[i]) + "', found: '" + terms.display(rule.premises[i]) + "'.");
        }
        return thm;
    }
    
    print(term : string) {
        const t = this.parse(term);
        if (t === undefined) this.reportError("Cannot parse term: '" + term + "'.");
        validateTerm(this.currentTheory.sig, this.currentTheory.terms, t);
        console.log("| " + this.currentTheory.terms.display(t));
    }

    printTeX(term : string) {
        const t = this.parse(term);
        if (t === undefined) this.reportError("Cannot parse term: '" + term + "'.");
        validateTerm(this.currentTheory.sig, this.currentTheory.terms, t);
        console.log("| " + displayTermAsTeX(this.currentTheory.terms, t));
    }

    theorem(label : string) : Theorem<Id, Term> {
        return this.currentTheory.theorem(this.currentTheory.terms.mkId(label));
    }

    assume(prop : string) : Theorem<Id, Term> {
        const t = this.parse(prop);
        if (t === undefined) this.reportError("Could not parse assumption '" + prop + "'.");
        return this.currentTheory.assume(t);
    }

    S(...varsAndTerms : (string | Term)[]) : Subst<Id, Term> {
        if (varsAndTerms.length % 2 !== 0)
            throw new Error("Even number of arguments required to make substitution.");
        let subst : Subst<Id, Term> = newSubst(this.currentTheory.terms.ids);
        for (let i = 0; i < varsAndTerms.length; i += 2) {
            const idStr = varsAndTerms[i];
            if (typeof idStr !== "string") throw new Error("variable must be a string");
            const id = this.currentTheory.terms.mkId(idStr);
            const termArg = varsAndTerms[i+1];
            const template = typeof termArg === "string" ? this.parse(termArg) : termArg;
            if (template === undefined)
                throw new Error("S: cannot parse template '" + varsAndTerms[i+1] + "'.");
            const arity = this.currentTheory.terms.arityOfTemplate(template);
            subst = addSubst(subst, id, arity, template);
        }
        return subst;
    }

    subst(subst : Subst<Id, Term>, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        return this.currentTheory.subst(subst, theorem);
    }

    add(term : string, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        const t = this.parse(term);
        if (t === undefined) throw new Error("add: Cannot parse term.");
        return this.currentTheory.add(t, theorem);
    }

    #computeBinders(template : Term, target : Term) : Binder<Id>[] {
        const terms = this.currentTheory.terms;
        const [templateBinders, templateBody] = terms.destTemplate(template);
        const [targetBinders, _] = terms.destTemplate(target);
        const binders : Binder<Id>[] = [];
        for (const x of targetBinders) {
            const i = templateBinders.findIndex(y => terms.ids.equal(x, y));
            if (i < 0) binders.push({var: x}); else binders.push({index: i});
        }
        return binders;
    }

    bind(template : string, target : string, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        const templateT = this.parse(template);
        if (templateT === undefined) this.reportError("bind: Cannot parse template.");
        const targetT = this.parse(target);
        if (targetT === undefined) this.reportError("bind: Cannot parse target binders.");
        const binders = this.#computeBinders(templateT, targetT);
        return this.currentTheory.bind(templateT, binders, theorem);
    }

    varElim(id : string, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        return this.currentTheory.varElim(this.currentTheory.terms.mkId(id),
            theorem);
    }

    infer(template : string | Term, general : Theorem<Id, Term>,
        specific : Theorem<Id, Term>) : Theorem<Id, Term>
    {
        const templateT = this.parse(template);
        if (templateT === undefined)
            this.reportError("infer: Cannot parse template.");
        return this.currentTheory.infer(templateT, general, specific);
    }

    ruleTeX(rule : Rule<Term>) : string {
        return this.#ruleTeXWith(this.currentTheory, rule);
    }

    #formatLabel(label : string) : string {
        const idx = label.indexOf('_');
        if (idx < 0) return "\\textsc{" + label + "}";
        const base = label.substring(0, idx);
        const sub = label.substring(idx + 1);
        if (/^\d+$/.test(sub)) {
            return "\\textsc{" + base + "}_{" + sub + "}";
        } else {
            const escapedSub = sub.replace(/_/g, "\\_");
            return "\\textsc{" + base + "}_{\\textsc{" + escapedSub + "}}";
        }
    }

    theoryTeX(theoryName : string) : string {
        const info = this.#theoryLocalInfo.get(theoryName);
        if (info === undefined)
            this.reportError("No local info for theory '" + theoryName + "'.");
        const theoryId = this.currentTheory.terms.mkId(theoryName);
        const thy = this.theories.get(theoryId);
        if (thy === undefined)
            this.reportError("No theory named '" + theoryName + "'.");

        const ids = thy.terms.ids;

        // Collect declarations comment
        const declLines : string[] = [];
        for (const spec of info.declarations) {
            declLines.push("%   " + displayAbsSigSpec(ids, spec));
        }

        // Collect all labeled rules with their TeX
        const entries : { label: string, ruleTeX: string }[] = [];
        for (const labelId of info.axioms) {
            const r = thy.theorem(labelId).proof.rule;
            entries.push({ label: ids.display(labelId), ruleTeX: this.#ruleTeXWith(thy, r) });
        }
        for (const labelId of info.definitions) {
            const r = thy.theorem(labelId).proof.rule;
            entries.push({ label: ids.display(labelId), ruleTeX: this.#ruleTeXWith(thy, r) });
        }
        for (const labelId of info.theorems) {
            const r = thy.theorem(labelId).proof.rule;
            entries.push({ label: ids.display(labelId), ruleTeX: this.#ruleTeXWith(thy, r) });
        }

        // Build LaTeX with subfigure layout
        const lines : string[] = [];
        lines.push("% Theory: " + theoryName + " — Generated by Paperweight");
        lines.push("%");
        if (declLines.length > 0) {
            lines.push("% Declarations:");
            lines.push(...declLines);
        }
        lines.push("\\begin{figure}[t]");
        lines.push("\\footnotesize");
        lines.push("\\centering");

        for (let i = 0; i < entries.length; i++) {
            const e = entries[i];
            lines.push("\\begin{subfigure}[b]{\\textwidth}");
            lines.push("\\centering");
            lines.push("$" + e.ruleTeX + "$");
            lines.push("\\caption{" + this.#formatLabel(e.label) + "}");
            lines.push("\\label{rule:" + e.label + "}");
            lines.push("\\end{subfigure}");
            if (i < entries.length - 1) {
                lines.push("\\\\[\\theorygap]");
            }
        }

        lines.push("\\caption{" + theoryName + "}");
        lines.push("\\label{fig:thy-" + theoryName + "}");
        lines.push("\\end{figure}");

        return lines.join("\n");
    }

    #ruleTeXWith(thy : Theory<Id, Term>, rule : Rule<Term>) : string {
        const terms = thy.terms;
        const premTexts = rule.premises.map(p => displayTermAsTeX(terms, p));
        const conclusion = displayTermAsTeX(terms, rule.conclusion);

        if (premTexts.length === 0) {
            return conclusion;
        }

        const totalPremLength = premTexts.reduce((sum, p) => sum + p.length, 0);
        let premisesStr : string;
        if (premTexts.length >= 3 || totalPremLength > 150) {
            // Vertical stacking for many or long premises
            premisesStr = "\\begin{gathered}" + premTexts.join(" \\\\ ") + "\\end{gathered}";
        } else {
            premisesStr = premTexts.join(" \\inferspace ");
        }

        return "\\inferrule{" + premisesStr + "}{" + conclusion + "}";
    }

}
