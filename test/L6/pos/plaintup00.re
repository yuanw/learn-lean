type pair('a, 'b) =
  | MkPair(x:'a, y:'b)
  ;

/*@ val myTuple: junk:int => pair(int[v|0 < v], int[v|v < 0]) */
let myTuple = (junk) => {
  let x0 = 5;
  let y0 = 0-5;
  MkPair(x0, y0)
};
