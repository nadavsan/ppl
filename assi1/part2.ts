import { setMaxListeners } from "process";
import * as R from "ramda";

const stringToArray = R.split("");

/* Question 1 */
const countLetters: (s: string) => Map<string,number> = 
(s: string): Map<string,number> => {
    const arr: string[] = s.split(""); 
    const map: {[index:string] : never | number} =  arr.reduce((acc: {[index:string] : never | number}, curr: string) => { //acc is the map, curr are the letters in the array
      //curr.charCodeAt(0) gives the ascii code of the current char we are looking at
        if(curr.charCodeAt(0) > 96 && curr.charCodeAt(0) < 123){//small letter
        if (acc[curr]) { //is the current char already in the map?
            acc[curr] += 1; //if yes increase its value
          } 
          else {
            acc[curr] = 1;} //else add it to the map with value 1
      }
      //checks if the curr char is a cap letter
      else if(curr.charCodeAt(0) > 64 && curr.charCodeAt(0) < 91){//cap letter
        const smallAscii : string = String.fromCharCode(curr.charCodeAt(0) + 32); //gets the small letter of a cap letter
        if (acc[smallAscii]) { //is the equivalent small letter in the map?
            acc[smallAscii] += 1;
          } 
          else {
            acc[smallAscii] = 1;}
      }
      return acc;}, {})
    return map;
}

/* Question 2 */
const isPaired: (s: string) => boolean = (s: string):boolean =>{
    const arr1: string[] = s.split("");
    const arr2: string[] = arr1.filter(x => (x == "(") || (x == ")") || (x == "[") || (x == "]") || (x == "{") || (x == "}")) 
    const arr3: number[] = arr2.reduce((acc:number[], element:string) => {
        //acc[0] keeps track of the last index in arr2 that holds an opening bracket that hasn't been "matched". This allows us to mimic a stack in some way 
        //acc[1] holds the number of brackets matched in arr2
        //acc[2] holds the boolean state(0 or 1) for if the array of brackets is balanced
        //note that acc[2] will be true given the array (,),) therefore we will also check that the number of opening brackets equals the number of closing brackets
        if(element == "(" || element == "[" || element == "{"){
            acc[0] = acc[0] + 1;
        }
        if(element == ")"){
            if(acc[0] < 0 || acc[0] > arr2.length){
              acc[2] = 0;
            }
            else if(arr2[acc[0]] != "("){
                acc[2] = 0;
            }
            acc[0] = acc[0] - 1;
            acc[1] = acc[1] + 1;
        }
        if(element == "]"){
            if(acc[0] < 0 || acc[0] > arr2.length){
              acc[2] = 0;
            }
            else if(arr2[acc[0]] != "["){
                acc[2] = 0;
            }
            acc[0] = acc[0] - 1;
            acc[1] = acc[1] + 1;
        }
        if(element == "}"){
            if(acc[0] < 0 || acc[0] > arr2.length){
              acc[2] = 0;
            }
            else if(arr2[acc[0]] != "{"){
                acc[2] = 0;
            }
            acc[0] = acc[0] - 1;
            acc[1] = acc[1] + 1;
        }
    return acc;}, [-1,0,1]);
    return ((arr3[1] == arr2.length / 2) && (arr3[2] == 1))
}
    


/* Question 3 */
export interface WordTree {
    root: string;
    children: WordTree[];
}

const treeToArray:(t:WordTree)=>string[]=
(t:WordTree)=>
  (t.children === [])?
    [t.root]
    :[t.root].concat(R.reduce(acc:string,curr:wordTree) =>
    );

/*const treeToArray = (t: WordTree, name:string): string[] =>{
  if(t.children === [])
    return [t.root];
  const arr1: string[] = R.reduce(acc:Number,curr:WordTree) => 
  const s:string[] = [t.root].concat(R.reduce(name:string,tree:WordTree) => name + ' ' + treeToArray(tree,'') , '' + tree.children);)
  return s;
}*/
export const treeToSentence = (t: WordTree): string => {
  const out: string[] = treeToArray(t,t.root);
  return out.join(' ');
}

