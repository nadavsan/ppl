import {  Binding, CExp, Exp, isLetPlusExp, isProgram, LetExp, LetPlusExp, makeLetExp, makeLetPlusExp, Program } from "./L31-ast";
import { Result, makeFailure, makeOk ,bind, mapv} from "../shared/result";
import { first, second, rest, allT, isEmpty } from "../shared/list";
import * as L31 from "./L31-ast";
import { concat, map, reduce } from "ramda";
import { parse as p } from "../shared/parser";
import { parseL3, parseL3Exp } from '../imp/L3-ast';
import { makeEmptySExp, makeSymbolSExp, SExpValue, makeCompoundSExp, compoundSExpToString, closureToString, isClosure, Value, isEmptySExp, isSymbolSExp, isCompoundSExp} from '../imp/L3-value'
import { isNumber, isArray, isString } from '../shared/type-predicates';

/*
Purpose: Transform L3 AST to JavaScript program string
Signature: l30ToJS(l2AST)
Type: [EXP | Program] => Result<string>
*/
export const l30ToJS = (exp: Exp | Program): Result<string>  => 
    makeOk(l30ToJSstring(exp)); 

const unparseLExps = (les: Exp[]): string =>
    map(l30ToJSstring, les).join(" "); 

const unparseProgramExps = (les: Exp[]): string =>
    map(l30ToJSstring, les).join(";\n"); 

const unparseLitExp = (le: L31.LitExp): string =>{
    return isEmptySExp(le.val) ? `'()` :
    isSymbolSExp(le.val) ?
        valueToString(le.val) === '=' ?
            `${valueToString('===')}`:
        `${valueToString(le.val)}` :
    isCompoundSExp(le.val) ? `'${valueToString(le.val)}` :
    `${le.val}`;
}

//a procExp is a lambda exp
const unparseProcExp = (procExp: L31.ProcExp): string =>{
    //map receives the lambda's arguments and pulls out their values, this will return an array which is then turned into a string seperated by commas
    return `((${map((p: L31.VarDecl) => p.var, procExp.args).join(",")}) ${'=>'} ${unparseLExps(procExp.body)})`
}

export const valueToString = (val: Value): string =>
    isNumber(val) ?  val.toString() :
    val === true ? 'true' :
    val === false ? 'false' :
    isString(val) ? `"${val}"` :
    isClosure(val) ? closureToString(val) :
    L31.isPrimOp(val) ? val.op :
    isSymbolSExp(val) ? `Symbol.for("${val.val}")`:
    isEmptySExp(val) ? "'()" :
    isCompoundSExp(val) ? compoundSExpToString(val) :
    val;

// returns the equivalent js prim op
// <prim-op>  ::= + | - | * | / | < | > | = | not |  and | or | eq? | string=? | number? | boolean? | symbol? | string?
const unparsePrimOpExp = (op: string): string =>{
    return op === '='? '===':
        op === 'eq?'? '===':
        op === 'not'? '!':
        op === 'and'? '&&':
        op === 'or'? '||':
        op === 'number?'? '((x) => (typeof(x) === number))':
        op === 'boolean?'? '((x) => (typeof(x) === boolean))':
        op === 'symbol?'? '((x) => (typeof (x) === symbol))':
        op === 'string?'? '((x) => (typeof (x) === string))':
        op === 'string=?'? '===':
        op;
    }

//parses an AppExp, an AppExp is a function applied directly, using a lambda or a prim op. each case is dealt differently
const unparseAppExp = (exp: L31.AppExp): string =>{
    return L31.isPrimOp(exp.rator)? `(${unparseAppExpRec(exp.rator, exp.rands)})`:
            L31.isProcExp(exp.rator) ? `${unparseProcExp(exp.rator)}(${map((rand:CExp):string => l30ToJSstring(rand), exp.rands).join(",")})`:
            (L31.isVarRef(exp.rator) && exp.rator.var === 'L3')? `${exp.rator.var}(${map((rand:CExp):string => l30ToJSstring(rand), exp.rands).join("\n")})`:
            L31.isVarRef(exp.rator)? `${exp.rator.var}(${map((rand:CExp):string => l30ToJSstring(rand), exp.rands).join(",")})`:
            "otherAppExp"
}

//this function is used for prim op functions
//we use a recursive function since we want to insert the operator(and a space char) between each two operands. for ex. (* 1 2 3) => (1 * 2 * 3)
const unparseAppExpRec = (rator: CExp, rands: CExp[]): string =>{
        return (rands.length === 1 && l30ToJSstring(rator) === '!')? concat('!', l30ToJSstring(rands[0])):
            rands.length === 1? l30ToJSstring(rands[0]): 
            concat(concat(concat(l30ToJSstring(rands[0]),' ') , concat(l30ToJSstring(rator),' ')), unparseAppExpRec(rator, rest(rands)));
}
    
const unparseLetExp = (le: LetExp) : string => {
    return `((${map((b: Binding) => `${b.var.var}`, le.bindings).join(",")}) => ${unparseLExps(le.body)})(${map((b: Binding) => `${l30ToJSstring(b.val)}`, le.bindings).join(",")})`
}       
            
export const l30ToJSstring = (exp: Exp | Program): string => {
    return L31.isBoolExp(exp) ? valueToString(exp.val) :
    L31.isNumExp(exp) ? valueToString(exp.val) :
    L31.isStrExp(exp) ? valueToString(exp.val) :
    L31.isLitExp(exp) ? unparseLitExp(exp) :
    L31.isVarRef(exp) ? exp.var :
    L31.isProcExp(exp) ? unparseProcExp(exp) :
    L31.isIfExp(exp) ? `(${l30ToJSstring(exp.test)} ? ${l30ToJSstring(exp.then)} : ${l30ToJSstring(exp.alt)})`:
    L31.isAppExp(exp) ? `${unparseAppExp(exp)}`  :
    L31.isPrimOp(exp) ? unparsePrimOpExp(exp.op) :
    L31.isLetExp(exp) ? unparseLetExp(exp) :
    L31.isDefineExp(exp) ? `const ${exp.var.var} = ${l30ToJSstring(exp.val)}` :
    L31.isProgram(exp) ? `${unparseProgramExps(exp.exps)}` :
    'exp';
}

const l30toJSResult = (x: string): Result<string> =>
    bind(bind(p(x), parseL3Exp), l30ToJS);