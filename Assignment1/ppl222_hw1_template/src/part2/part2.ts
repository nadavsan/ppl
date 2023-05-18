import { setMaxListeners } from "process";
import * as R from "ramda";

const stringToArray = R.split("");

/* Question 1 */
export const countLetters: (s: string) => {} = (s: string): {} => {
    const isLetter = (c:string): boolean => { return ((c.charCodeAt(0) > 96 && c.charCodeAt(0) < 123) || (c.charCodeAt(0) > 64 && c.charCodeAt(0) < 91));}
    const arr1: string[] = stringToArray(s);
    const arr2: string[] = R.filter(isLetter, arr1);
    return R.countBy(R.toLower)(arr2);
}

/* question 2 */
const openBracketPred: (x: string) => boolean = (x:string): boolean =>{ 
    return ((x == "(") || (x == "[")|| (x == "{"));
}

const closingBracketPred: (x:string) => boolean = (x:string): boolean =>{
    return ((x == ")") || (x == "]")|| (x == "}"));
}
//returns true if two brackets match, for example () or []
const matchingBrackets: (opening:string, closing:string) => boolean = (opening:string, closing:string):boolean =>{
    return(R.equals(opening.charCodeAt(0) + 1, closing.charCodeAt(0)) || R.equals(opening.charCodeAt(0) + 2, closing.charCodeAt(0)))
}

const isPairedRec: (arr: string[]) => boolean = (arr: string[]): boolean =>{
    if(arr.length === 0){
        return true;
    }
    const closingIndex:number = R.findIndex(closingBracketPred, arr); //get index of the first closing bracket
    if(R.equals(-1, closingIndex)){ //if no closing bracket exists return false
        return false;
    }
    const arr2:string[] = R.slice(0,closingIndex,arr); //temp array used to find the last opening bracket's index, smaller than 'closingindex'
    const openingIndex:number = R.findLastIndex(openBracketPred, arr2);
    if(R.equals(-1, openingIndex)){ //if no opening bracket exists return false
        return false;
    }
    if(!matchingBrackets(arr[openingIndex], arr[closingIndex])){ //return false if both brackets found don't match
        return false;
    }
    else{ 
        const arr3: string[] = R.remove(closingIndex, 1, arr); //remove both brackets from the array
        const arr4:string[] = R.remove(openingIndex, 1, arr3); 
        return isPairedRec(arr4); //recursion step
    }
}

export const isPaired: (s: string) => boolean = (s: string):boolean =>{
    const arr1: string[] = s.split("");
    const arr2: string[] = arr1.filter(x => (x == "(") || (x == ")") || (x == "[") || (x == "]") || (x == "{") || (x == "}")); 
    return isPairedRec(arr2);
}   

/* Question 3 */
export interface WordTree {
    root: string;
    children: WordTree[];
}

export const treeToSentence = (t: WordTree): string => {
    if(t.children.length === 0){
        return t.root;
    }
    else{
        return  R.reduce((acc: string, curr: WordTree) => acc + " " + treeToSentence(curr), t.root, t.children);
    }
}
//