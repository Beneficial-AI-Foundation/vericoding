predicate ValidInput(n: int, a: int, b: int)
{
  n > 0 && a > 0 && b > 0
}

predicate ValidOutput(result: seq<int>, n: int, a: int, b: int)
{
  |result| == 3 &&
  result[0] >= 6 * n &&
  result[1] > 0 && result[2] > 0 &&
  result[0] == result[1] * result[2] &&
  ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}

// <vc-helpers>
lemma FindFactors(n: int, a: int, b: int) 
  requires n > 0 && a > 0 && b > 0
  ensures exists w, h :: (w * h >= 6 * n) && ((w >= a && h >= b) || (w >= b && h >= a))
{
  var min_area := 6 * n;
  var w := max(a, b);
  var h := (min_area + w - 1) / w;
  if h < min(a, b) {
    h := min(a, b);
    w := (min_area + h - 1) / h;
    if w < max(a, b) {
      w := max(a, b);
    }
  }
  assert w * h >= min_area;
  assert (w >= a && h >= b) || (w >= b && h >= a);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var min_area := 6 * n;
  var required_width := max(a, b);
  var required_height := (min_area + required_width - 1) / required_width;
  
  if required_height < min(a, b) {
    required_height := min(a, b);
    required_width := (min_area + required_height - 1) / required_height;
    if required_width < max(a, b) {
      required_width := max(a, b);
    }
  }
  
  var area := required_width * required_height;
  result := [area, required_width, required_height];
}
// </vc-code>

