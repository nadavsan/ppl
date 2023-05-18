import { Result, makeFailure, makeOk, bind, either } from "../lib/result";
import * as R from "ramda";

/* Library code */
const findOrThrow = <T>(pred: (x: T) => boolean, a: T[]): T => {
    for (let i = 0; i < a.length; i++) {
        if (pred(a[i])) return a[i];
    }
    throw "No element found.";
}

export const findResult = <T>(pred: (x: T) => boolean, a: T[]): Result<T> => {
    const arr: T[] = R.filter((x:T) => pred(x), a);
    if(arr.length === 0){
        return makeFailure("No element found.");
    }
    else{
        return makeOk(arr[0]);
    }
    //return arr.length===0 ? makeFailure("error") : makeOk(arr[0])
}

/* Client code */
const returnSquaredIfFoundEven_v1 = (a: number[]): number => {
    try {
        const x = findOrThrow(x => x % 2 === 0, a);
        return x * x;
    } catch (e) {
        return -1;
    }
}

export const returnSquaredIfFoundEven_v2 = (a: number[]) : Result<number> => {
    const res: Result<number> = findResult(x => x%2 === 0, a);
    return bind(res, x => makeOk(x*x));
}

export const returnSquaredIfFoundEven_v3 = (a: number[]) : number => {
    const res: Result<number> = findResult(x => x%2 === 0, a);
    return either(res, x => x*x, x => -1);
}
//