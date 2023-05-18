import {  Binding, CExp, Exp, isLetPlusExp, isProgram, LetExp, LetPlusExp, makeLetExp, makeLetPlusExp, Program } from "./L31-ast";
import { Result, makeFailure, makeOk ,bind, mapv} from "../shared/result";
import { first, second, rest, allT, isEmpty } from "../shared/list";
import * as L31 from "./L31-ast";
import { concat, map, reduce } from "ramda";


/*
Purpose: Transform L31 AST to L3 AST
Signature: l31ToL3(l31AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
export const L31ToL3 = (exp: Exp | Program): Result<Exp | Program> =>
    // isProgram(exp) && isLetPlusExp(exp.exps[0])?makeOk(reWriteLetPlusExp(exp.exps[0])):
    L31.isExp(exp) ? makeOk(rewriteAllLetPlusExp(exp)) :
    isProgram(exp) ? makeOk(L31.makeProgram(map(rewriteAllLetPlusExp, exp.exps))) :
        makeOk(exp);

export const rewriteLetPlusExp = (exp: LetPlusExp) : LetExp => 
    (exp.bindings.length <= 1)? makeLetExp(exp.bindings, exp.body): 
    makeLetExp([exp.bindings[0]], [rewriteLetPlusExp(makeLetPlusExp(rest(exp.bindings), exp.body))])

export const reWriteLetPlusExpResult = (exp: LetPlusExp) : Result<LetExp> => 
    makeOk(rewriteLetPlusExp(exp));    

export const rewriteAllLetPlusExp = (exp: Exp):Exp =>
    L31.isCExp(exp) ? rewriteAllLetPlusCExp(exp) :
    L31.isDefineExp(exp) ? L31.makeDefineExp(exp.var,
    rewriteAllLetPlusCExp(exp.val)) :
        exp;    

const mergeBindings = (vars:string[], vals:CExp[]) : Binding[] => {
    if(vars.length === 1 || vals.length === 1){
        return [L31.makeBinding(first(vars), first(vals))]
    }
    else{
        return concat([L31.makeBinding(first(vars), first(vals))], mergeBindings(rest(vars), rest(vals)))
    }
}
         
export const rewriteLetExp = (bindings: L31.Binding[]) : L31.Binding[] => {
    const vars:string[] = map(b => b.var.var, bindings);
    const vals = map(b => b.val, bindings);
    const vals2 = map(rewriteAllLetPlusCExp, vals);
    return mergeBindings(vars, vals2);
}

export const rewriteAllLetPlusCExp = (exp: L31.CExp): L31.CExp => 
    L31.isAtomicExp(exp) ? exp :
    L31.isLitExp(exp) ? exp :
    L31.isIfExp(exp) ? L31.makeIfExp(rewriteAllLetPlusCExp(exp.test),
    rewriteAllLetPlusCExp(exp.then),
    rewriteAllLetPlusCExp(exp.alt)) :
    L31.isAppExp(exp) ? L31.makeAppExp(rewriteAllLetPlusCExp(exp.rator),
    map(rewriteAllLetPlusCExp, exp.rands)) :
    L31.isProcExp(exp) ? L31.makeProcExp(exp.args,
    map(rewriteAllLetPlusCExp, exp.body)) :
    L31.isLetExp(exp)? L31.makeLetExp(rewriteLetExp(exp.bindings), map(rewriteAllLetPlusCExp, exp.body))  :
    L31.isLetPlusExp(exp) ? rewriteAllLetPlusCExp(rewriteLetPlusExp(exp)) :
        exp;