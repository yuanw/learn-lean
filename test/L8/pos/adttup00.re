type pair('a, 'b) =
  | MkPair(x:'a, y:'b) => [v|v = MkPair(x, y)]
  ;

/*@ val myTuple: junk:int => pair(int, int)[v| v = MkPair(5, -5)] */
let myTuple = (junk) => {
  let x0 = 5;
  let y0 = 0-5;
  MkPair(x0, y0)
};
