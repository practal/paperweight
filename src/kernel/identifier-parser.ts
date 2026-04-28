import { rep1P, orP, literalP, tagP, seqP, repP, lookaheadP, optP } from "@practal/parsing";
import { P, charTestP } from "@practal/rx";
import { isUnicodeLetter, isUnicodeDigit } from "things";

export enum IdentifierTag {
    id = "id",
    shortid = "shortid",
    command = "command",
    dot = "dot",
    tilde = "tilde",
    script = "script"
}   

const letterP : P = charTestP(isUnicodeLetter);
const digitP : P = charTestP(isUnicodeDigit);
const fragmentP : P = rep1P(orP(letterP, digitP));
const hyphenP : P = orP(literalP("-"), literalP("‐"));
const tildeP : P = tagP(IdentifierTag.tilde, literalP("~"));
const separatorP : P = orP(hyphenP, tildeP);
const wordP : P = seqP(fragmentP, repP(separatorP, fragmentP));
const scriptP : P = tagP(IdentifierTag.script, orP(literalP("_"), literalP("^")));
const commandP : P = tagP(IdentifierTag.command, seqP(literalP("\\"), fragmentP));
const dotP : P = tagP(IdentifierTag.dot, literalP("."));
const shortIdP : P = tagP(IdentifierTag.shortid, seqP(
    lookaheadP(letterP),
    wordP,
    repP(scriptP, wordP)));
export const identifierP : P = tagP(IdentifierTag.id, seqP(
    shortIdP,
    repP(dotP, shortIdP),
    optP(commandP)));