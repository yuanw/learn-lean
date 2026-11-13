type pair('a, 'b)(p : 'a => 'b => bool) =
  | MkPair(x:'a, y:'b[v|p x v])
  ;

/*@ val myTuple: junk:int => pair(int[v|0 < v], int[v|v < 0])((u:int, v:int) => u + v == 0) */
let myTuple = (junk) => {
  let x0 = 5;
  let y0 = 0-5;
  MkPair(x0, y0)
};
