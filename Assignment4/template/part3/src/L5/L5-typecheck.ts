// L5-typecheck
// ========================================================
import { equals, filter, flatten, includes, map, intersection, zipWith, reduce, forEach } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, unparse, parseL51,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp, SetExp, LitExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isSetExp, isLitExp, 
         isDefineTypeExp, isTypeCaseExp, DefineTypeExp, TypeCaseExp, CaseExp, makeProgram, makeLitExp, VarDecl } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp, Record,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, UserDefinedTExp, isUserDefinedTExp, UDTExp, 
         isNumTExp, isBoolTExp, isStrTExp, isVoidTExp,
         isRecord, ProcTExp, makeUserDefinedNameTExp, Field, makeAnyTExp, isAnyTExp, isUserDefinedNameTExp, isTupleTExp, isNonEmptyTupleTExp,
         LitTExp, makeLitTExp, isLitTExp} from "./TExp";
import { isEmpty, allT, first, rest, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, mapv, mapResult, isFailure, either, isOk } from '../shared/result';
import { isErrored } from 'stream';

// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
        isEmpty(tail) ? [] :
        isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
        isEmpty(tail) ? [] :
        isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends {typeName: string}>(typeName: string, items: T[]): Result<T> =>
    isEmpty(items) ? makeFailure(`${typeName} not found`) :
    first(items).typeName === typeName ? makeOk(first(items)) :
    getItemByName(typeName, rest(items));

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51
// Is te1 a subtype of te2?
const isSubType = (te1: TExp, te2: TExp, p: Program): boolean =>
    equals(te1, te2) ? true: //this line was added so that we can recursively keep using isSubType which doesn't carry exp
    isAnyTExp(te2)? true:
    isRecord(te1) && isUserDefinedTExp(te2)? (getRecordParents(te1.typeName, p).filter((val) => {return (val.typeName === te2.typeName)}).length != 0):
    isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)? isUserDefinedNameTExpAux(te1, te2, p): 
    isProcTExp(te1) && isProcTExp(te2) ? 
    te1.paramTEs.length === te2.paramTEs.length &&
    !zipWith((x: TExp, y: TExp) => {return isSubType(te1, te2, p)}, te1.paramTEs, te2.paramTEs).includes(false) &&
    isSubType(te1.returnTE, te2.returnTE, p):
    false;

//an aux function added which is used if te1, te2 are both UserDefinedNameTExp
const isUserDefinedNameTExpAux: (te1: TExp, te2: TExp, p: Program) => boolean = (te1: TExp, te2: TExp, p: Program) : boolean =>{
    if(isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)){
        const x1 = getTypeByName(te1.typeName, p);
        const x2 = getTypeByName(te2.typeName, p);
        if(isOk(x1) && isOk(x2)){
            const y1 = x1.value;
            const y2 = x2.value;
            if(isRecord(y1) && isUserDefinedTExp(y2)){
                return (getRecordParents(y1.typeName, p).filter((val) => {return (val.typeName === y2.typeName)}).length != 0);
            }
            else if(isRecord(y1) && isRecord(y2)){
                return y1.typeName === y2.typeName;
            }
            else if(isUserDefinedTExp(y1) && isUserDefinedTExp(y2)){
                return y1.typeName === y2.typeName;
            }
        }
    }
    return false;
}

// TODO L51: Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names 
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> =>
  isSubType(te1, te2, p)? makeOk(te2):
  equals(te1, te2) ? makeOk(te2) :
  makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
    isProcTExp(te) ? [te] :
    isUserDefinedTExp(te) ? [te] :
    isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
    isUserDefinedNameTExp(te) ?
        either(getUserDefinedTypeByName(te.typeName, p),
                (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                (_) => either(getRecordByName(te.typeName, p),
                            (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName), 
                                                  map((ud) => makeUserDefinedNameTExp(ud.typeName), 
                                                      getRecordParents(rec.typeName, p))),
                            (_) => [])) : 
    [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] =>  {
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
    const parentsList : TExp[][] = map((t) => getParentsType(t,p), types);
    return reduce<TExp[], TExp[]>(intersection, first(parentsList), rest(parentsList));
}

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number  
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min, 
            makeAnyTExp(),
            types);

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
    makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation

//added - an auxiliary function that returns a TExp array that contains all types of a given record
export const getFieldTexp = (record: Record): TExp[] => {
    return map((x: Field): TExp => {return x.te} , record.fields)
}

// TOODO L51
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)
export const initTEnv = (p: Program): TEnv => {
    //initialize an extended TEnv
    const emptyTE = makeEmptyTEnv();
    var te = makeExtendTEnv([], [makeVoidTExp()], emptyTE)
    //get typedefinitions
    //for each typedefinition
    //extEnv(field:typedef.name+ "?" , makeProcTExp([makeAnyTexp()],makeBooleanTexp))
    const TypeDefs = getTypeDefinitions(p);
    for(var i = 0; i < TypeDefs.length; i++){
        te = makeExtendTEnv([TypeDefs[i].typeName + "?"], [makeProcTExp([makeAnyTExp()], makeBoolTExp())], te);
    }
    //for each record
    //extEnv(field:record.name+ "?" , makeProcTExp([makeAnyTexp()],makeBooleanTexp))
    //extEnv(field:"make-" + record.name , makeProcTExp([map(getTexp,record.fields)],makeuserdefinenameTexp(record.name)))
    const records = getRecords(p);
    for(var i = 0; i < records.length; i++){
        te = makeExtendTEnv([records[i].typeName + "?"], [makeProcTExp([makeAnyTExp()], makeBoolTExp())], te);
        te = makeExtendTEnv(["make-" + records[i].typeName], [makeProcTExp(getFieldTexp(records[i]), makeUserDefinedNameTExp(records[i].typeName))], te);
    }
    const defs = getDefinitions(p);
    for(var i = 0; i < defs.length; i++){
        te = makeExtendTEnv([defs[i].var.var], [defs[i].var.texp], te);
    }
    return te;
}

const checkUserDefinedTypesCheck1 = (records: Record[], p: Program): boolean =>{
    for(var i = 0; i<records.length; i++){
        const parents: UserDefinedTExp[] = getRecordParents(records[i].typeName, p);
        //go over the parnets recieved, from them get records[i] 
        var iRecord: Record[] = []; //this array will contain the same record, possibly from different parents
        var iRecordFiledsSet: Set<Field> = new Set<Field>(); //this array contains all fields from those parents
        for(var j = 0; j<parents.length; j++){
            const tempRecs: Record[] = parents[j].records.filter((rec: Record): boolean => {return rec.typeName === records[i].typeName}); //parents[i].records contains all records of the parents, from here we want only those matching records[i]
            for(var t = 0; t<tempRecs.length; t++){ //the tempRecs array should only contain 1 element, we add it to iRecord
                iRecord.push(tempRecs[t]); //add this apperance of the record to iRecord
                const recFileds: Field[] = tempRecs[t].fields;
                for(var y = 0; y < recFileds.length; y++){ //add the fields of the record's apperance to the set of fields
                    iRecordFiledsSet.add(recFileds[y]);
                }
            }
        }
        //check that every record recieved contains the same number of fields as the set
        if(iRecord.filter((rec: Record): boolean => {return rec.fields.length == iRecordFiledsSet.size}).length != iRecord.length){
          return false;
        }
        var iRecordFiledsArray: Field[] = []; //a copy of iRecordFiledsSet in the form of an array, which is needed in order to use the filter function
        iRecordFiledsSet.forEach((val: Field) : void => {iRecordFiledsArray.push(val)});
        for(var j = 0; j < iRecord.length; j++){ //go over all fields of a record in iRecord a approve that it contains all fields in iRecordFiledsArray
            const fields: Field[] = iRecord[j].fields;
            if(iRecordFiledsArray.filter((val:Field): boolean =>{return fields.includes(val)}).length != iRecordFiledsArray.length){
                return false;
              }
        }
    }
    return true;
}

//added - an aux function that checks if a given record contains a self userDefined field
const isSelfDefinedRecord = (record: Record, ud: UserDefinedTExp) : boolean => {
    const fields: Field[] = record.fields;
    //check if fields contains a field that is userDefiedType & equal to self userDefine
    //we do so by applying a filter to fields that keeps fields that fulfill the above
    //if there is such a field then the length of the fields after applying the filter is greater than zero and we return true
    if(fields.filter((field: Field) : boolean => {
        if(isUserDefinedTExp(field.te)){
            if(field.te.typeName === ud.typeName){
                return true;
            }
        }
        return false;
    }).length > 0){
        return true;
    }
    return false;
}

//added - an aux function that returns false if all records of a given UserDefinedTExp are self defined
const checkUserDefinedTypesCheck2 = (ud: UserDefinedTExp) : boolean => {
    const records: Record[] = ud.records;
    //return false if all records are self defined
    if(filter((record: Record) : boolean => {return isSelfDefinedRecord(record, ud)}, records).length == records.length){
        return false;
    }
    return true;
}

// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51
const checkUserDefinedTypes = (p: Program): Result<true> => {
    //check1:
    //If the same type name is defined twice with different definitions
    //get All records , for each record:
    //get parents , check for each parent: parent.record.fields are equal. 
    const records: Record[] = getRecords(p); //get all records in program
    if(!checkUserDefinedTypesCheck1(records, p)){
        return makeFailure("checkUserDefinedTypes check1 failed")
    }

    //check2:
    // If a recursive type has no base case
    // getAllDefines:
        // for each record : 
            //for each field: if all fields not user defiend - OK!
                            // if any field is userDefiedType - check if equal to self userDefine - if true is not OK!
        //if all records of a given UD are not OK: not OK!
    // over all, if there is a ud that contains a record that is not ok: not OK!
    const uds: UserDefinedTExp[] = getTypeDefinitions(p); //all User defines in the program
    if(uds.filter(checkUserDefinedTypesCheck2).length != uds.length){
        return makeFailure("checkUserDefinedTypes check2 failed")
    }
    return makeOk(true);
}
//added - an auxiliary function that gets all records from a given TypeCaseExp
const getRecordsFromTC = (tc: TypeCaseExp, p: Program): Record[] => {
    var records: Record[] = [];
    const cases: CaseExp[] = tc.cases;
    for(var i = 0; i< cases.length; i++){
        const res: Result<Record> = getRecordByName(cases[i].typeName, p);
        if(isOk(res)){
            records.push(res.value);
        }
    }
    return records;
}

// TODO L51
const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => {
    //Check 1:
    // get all subtypes of tc.typeName
    // Check that all type case expressions have exactly one clause for each constituent subtype
    // this includes that there are no more clauses for a Record
    const udResult: Result<UserDefinedTExp> = getUserDefinedTypeByName(tc.typeName, p);
    if(isOk(udResult)){
        const idRecords: Record[] = udResult.value.records;
        const tcRecords: Record[] = getRecordsFromTC(tc, p);
        const idRecordsNames: String[] = idRecords.map((rec: Record): String => {return rec.typeName});
        const tcRecordsNames: String[] = tcRecords.map((rec: Record): String => {return rec.typeName});
        //we run Check 1 by checking that idRecordsNames is a subset of tcRecordsNames and that tcRecordsNames is a subset of idRecordsNames
        //we do so by mapping both arrays to boolean array, and afterwards check if they include a false value
        if((idRecordsNames.map((rec: String) : boolean => {return tcRecordsNames.includes(rec)}).includes(false)) ||
           (tcRecordsNames.map((rec: String) : boolean => {return idRecordsNames.includes(rec)}).includes(false))){
               return makeFailure("checkTypeCase Check1 failed");
           }
    //check 2:
    //foreach caseExp: 
    //check if len(varDecls) == len(getRecord(typename).fields)
    //we do so by comparing the fields in both arrays using zipWith
        if(zipWith((x: CaseExp, y: Record): boolean => {return x.varDecls.length == y.fields.length} ,tc.cases, tcRecords).includes(false)){
            return makeFailure("checkTypeCase Check2 failed");
        };
        return makeOk(true);
    }
    return makeFailure("getUserDefinedTypeByName returned a failure result");
}
// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) =>
        bind(typeofExp(p, initTEnv(p), p), unparseTExp));

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv, p) :
    isProcExp(exp) ? typeofProc(exp, tenv, p) :
    isAppExp(exp) ? typeofApp(exp, tenv, p) :
    isLetExp(exp) ? typeofLet(exp, tenv, p) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
    isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
    isProgram(exp) ? typeofProgram(exp, tenv, p) :
    isSetExp(exp) ? typeofSet(exp, tenv, p) :
    isLitExp(exp) ? typeofLit(exp, tenv, p) :
    isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
    isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> =>
    isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
    bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// L51 Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
// 
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp, p)));
    return bind(constraint1, (_c1) => constraint2);
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args); //get texps of the function's arguments
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv); 
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) => 
                                                                checkEqualType(typeOfRand, trand, app, p)),
                                          app.rands, ratorTE.paramTEs);
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp, p)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - write the true definition
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    const v = exp.var.var;
    const texp = exp.var.texp;
    const val = exp.val;
    const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenvVal, p);    
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51
// TODO - Write the typing rule for DefineType expressions
// Purpose: compute the type of a DefineType expressions
// Typing rule: ( define-type <id> [ ( <id> <VarDecl>* ) ]* )
// For user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
// tenv-val = extend-tenv(id:<user-defined-name-te>; tenv)
// If type<record_1> = <record-te> ... type<record_n> = <record-te>
// then type<( define-type <id> [ ( <id> <VarDecl>* ) ]* )> = void
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    if(isFailure(checkUserDefinedTypes(_p))){
        console.log("checkUserDefinedTypes failed");
        return makeFailure("ud records aren't defined correctly");
    }
    const records : Record[] = exp.udType.records;
    if(records.filter((record: Record): boolean => {return isRecord(record)}).length != records.length){
        return makeFailure("ud records aren't defined correctly");
    }
    const name = exp.udType.typeName; 
    const texp = makeUserDefinedNameTExp(exp.udType.typeName); 
    const tenvVal = makeExtendTEnv([name], [texp], _tenv);
    return makeOk(makeVoidTExp());
}
    

// TODO L51
// Purpose: compute the type of set!
// Typing rule:
// (set! var val)
// if   type<var>(tenv) = t1
//      type<val>(tenv) = t1
// then type<(set! var val)>(tenv) = void
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    const var1 = exp.var;
    const val = exp.val;
    const varTE = typeofExp(var1, _tenv, _p);
    const valTE = typeofExp(val, _tenv, _p);
    const constraint2 = bind(varTE, (varTE: TExp) =>
        bind(valTE, (valTE: TExp) =>
        checkEqualType(varTE, valTE, exp, _p)));
    return mapv(constraint2, (_) => makeVoidTExp())
}

// TODO L51
// Purpose: compute the type of lit
// Typing rule:
// (quote <Sexp>)
// type<(quote <Sexp>)>(tenv) = literal
export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    // const sexp = exp.val;
    // const sexpTE = typeofExp(sexp, _tenv, _p); 
    return makeOk(makeLitTExp());
}

// added - an aux function that checks that all cluases return the same type, and if so - return it
const typeofTypeCaseCheck1 = (cases: CaseExp[], tenv: TEnv, p: Program): Result<TExp> =>{
    var caseBodyTypeRes: Result<TExp> = makeOk(makeVoidTExp());
    const casesTypesResult: Result<TExp>[] = cases.map((c: CaseExp): Result<TExp> => { 
        const vars: string[] = map((vd: VarDecl): string => {return vd.var} ,  c.varDecls)
        const record: Result<Record> = getRecordByName(c.typeName , p);
        var varTypes: TExp[] = [];
        if(isOk(record)){
            varTypes = record.value.fields.map((field:Field) => field.te)
        }
        const extTEnv = makeExtendTEnv(vars, varTypes, tenv)
        const caseType = typeofExps(c.body, extTEnv ,p);
        caseBodyTypeRes = caseType;
        return caseType;
    })
    var casesTypesSet: Set<string> = new Set<string>(); // a set is used inorder to make sure that all case cluases have the same return type
    for(var i = 0; i < casesTypesResult.length; i++){
        const caseRes: Result<TExp> = casesTypesResult[i];
        if(isOk(caseRes)){
            casesTypesSet.add(caseRes.value.tag) //this is something of the form circle, or NumExp etc. 
        }
        else{
            return makeFailure("failure recieved from casesTypesResult")};
    }
    if(casesTypesSet.size == 1){
        return caseBodyTypeRes; //all case cluases have the same return type
    }
    return makeFailure("TypeCase's clauses don't return the same type")
}


// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule: ( type-case <id> <CExp> ( <case-exp> )+  )
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  If (records record_1 ... record_n) == type-case's records
//      for each record_i in type-case:
//          record_i.fields == (field_11 ... field_1r1) 
//      for each body_i, body_j in type_case:
//          body_i.type == body_j.type
// then type<( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )> = body_1.type
export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {
    if(isFailure(checkTypeCase(exp, p))){
        return makeFailure("exp isn't a valid type case expression1");
    }
    const typeCaseTypeRes: Result<TExp> = typeofTypeCaseCheck1(exp.cases, tenv, p);
    if(isFailure(typeCaseTypeRes)){
        return makeFailure("exp isn't a valid type case expression2");
    }
    else{
        return typeCaseTypeRes;
    }
}
