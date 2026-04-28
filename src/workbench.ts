import { RedBlackMap } from "things";
import { defaultTerms, Id, newSubst, ProofKind, Rule, Subst, Term, Terms, Theorem, Theory, simpleSubstNoDangling, validateTerm, AxiomSource } from "./kernel/index.js";
import { Context } from "./context.js";
import { writeFileSync } from "node:fs";

export const context = new Context(defaultTerms, RedBlackMap(defaultTerms.ids));
export type Thm = Theorem<Id, Term>
export type S = Subst<Id, Term>

let sorryCount = 0;

let TeXMode : boolean = false;

export function setTeXMode(on : boolean) {
    TeXMode = on;
}

export function info() {
    context.info();
}

export function terms() : Terms<Id, Term> {
    return context.currentTheory.terms;
}

export function parse(term : string | Term) : Term | undefined {
    return context.parse(term);
}

export function theory() : Theory<Id, Term> {
    return context.theory();
}

export function beginTheory() {
    sorryCount = 0;
    context.beginTheory();
}

export function useTheory(theoryName : string) {
    context.importTheory(theoryName, false);
}

export function includeTheory(theoryName : string) {
    context.importTheory(theoryName, true);
}

export function displayId(id : Id) : string {
    return context.displayId(id);
}

export function endTheory(theoryName : string) {
    context.endTheory(theoryName);
    if (sorryCount > 0) {
        console.log("WARNING: " + sorryCount + " sorry" + (sorryCount > 1 ? "s" : "") + " remaining!");
        console.log("");
    }
}

export function restore(theoryName : string) {
    context.restore(theoryName);
}

export function declare(declaration : string) {
    context.declare(declaration);
}

export function validate(term : string) {
    context.validate(term);
}

export function display(term : Term) : string {
    return context.display(term);
}

export function printRule(label : string, rule : Rule<Term>) {
    context.printRule(label, rule);
}

export function axiom(label : string,
    conclusion : string, premises : string[] = [])
{
    context.axiom(label, conclusion, premises);
}

export function define(head : string, definiens : string)
{
    context.define(head, definiens);
}

export function defineAs(label : string, head : string, definiens : string)
{
    context.defineAs(label, head, definiens);
}

export function defineWith(relation : string, head : string, definiens : string)
{
    context.defineWith(relation, head, definiens);
}

export function defineWithAs(label : string, relation : string, head : string, definiens : string)
{
    context.defineWithAs(label, relation, head, definiens);
}

export function thm(label : string) : Thm {
    return context.theorem(label);
}

export function assume(prop : string) : Thm
{
    return context.assume(prop);
}

export function lemma(label : string, thm : Thm)
{
    context.lemma(label, thm);
}

export function have(label : string, conclusion : string, premises : string[], thm : Thm)
{
    context.have(label, conclusion, premises, thm);
}

export function note(conclusion : string, premises : string[], thm : Thm) : Thm
{
    return context.note(conclusion, premises, thm);
}

export function sorry(conclusion : string, premises : string[] = []) : Thm
{
    const tConclusion = context.parse(conclusion);
    if (tConclusion === undefined) throw new Error("sorry: cannot parse conclusion '" + conclusion + "'.");
    const tPremises = context.parseItems(s => "sorry: cannot parse premise '" + s + "'.", premises);
    validateTerm(context.currentTheory.sig, context.currentTheory.terms, tConclusion);
    for (const p of tPremises) validateTerm(context.currentTheory.sig, context.currentTheory.terms, p);
    const rule : Rule<Term> = { premises: tPremises, conclusion: tConclusion };
    const label = context.currentTheory.terms.mkId("sorry");
    const proof = { kind: ProofKind.Axiom as const, label, rule, source : AxiomSource.Sorry };
    sorryCount++;
    return { theory: context.currentTheory, proof };
}

export function conjecture(label : string, conclusion : string, premises : string[])
{
    have(label, conclusion, premises, sorry(conclusion, premises));
}

export function S(...varsAndTerms : (string | Term)[]) : S {
    return context.S(...varsAndTerms);
}

export function subst(s : S, thm : Thm) : Thm {
    return context.subst(s, thm);
}

export function add(term : string, thm : Thm) : Thm {
    return context.add(term, thm);
}

export function bind(template : string, target : string, thm : Thm) : Thm {
    return context.bind(template, target, thm);
}

export function varElim(id : string, theorem : Thm) : Thm {
    return context.varElim(id, theorem);
}

export function infer(general : Thm, specific : Thm) : Thm {
    const c = conclOf(specific);
    const t = terms();
    for (const p of premsOf(general)) {
        const [binders, body] = t.destTemplate(p);
        const args = binders.map(b => t.mkVarApp(b, []));
        const instantiated = simpleSubstNoDangling(t, 0, body, args);
        if (t.equal(instantiated, c)) {
            return context.infer(p, general, specific);
        }
    }
    throw new Error("infer: cannot find premise");
}

export function conclOf(thm : Thm) : Term {
    return thm.proof.rule.conclusion;
}

export function premsOf(thm : Thm) : Term[] {
    return thm.proof.rule.premises;
}

export function print(t : string | Thm) {
    if (typeof t === "string") {
        if (TeXMode)
            context.printTeX(t);
        else
            context.print(t);
    } else {
        printRule("Theorem", t.proof.rule);
    }
}

export function ruleTeX(thm : Thm) : string {
    return context.ruleTeX(thm.proof.rule);
}

export function theoryTeX(theoryName : string) : string {
    return context.theoryTeX(theoryName);
}

export function exportTeX(theoryName : string, filePath : string = "./tex/" + theoryName + ".tex") : void {
    const tex = context.theoryTeX(theoryName);
    writeFileSync(filePath, tex + "\n", "utf-8");
    console.log("Exported theory '" + theoryName + "' to " + filePath);
}

console.log("");
console.log("Paperweight — Workbench");
console.log("=============================");
console.log("");
