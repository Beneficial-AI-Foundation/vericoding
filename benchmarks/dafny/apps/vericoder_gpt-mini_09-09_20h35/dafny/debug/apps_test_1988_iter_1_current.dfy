predicate ValidInput(s: string)
{
    |s| >= 2 &&
    (s[|s|-1] == '\n' || (|s| >= 2 && s[|s|-2..] == "\n")) &&
    exists lines :: lines == split_lines(s) && |lines| >= 1 &&
    exists lines, t :: lines == split_lines(s) && t == parse_int(lines[0]) && t >= 1 &&
    (forall lines, t :: 
        (lines == split_lines(s) && t == parse_int(lines[0])) ==> 
        |lines| >= 1 + 2*t) &&
    (forall lines, t, i :: 
        (lines == split_lines(s) && t == parse_int(lines[0]) && 0 <= i < t) ==> 
        (exists n :: n == parse_int(lines[1 + 2*i]) && n >= 1 && n <= 5000 && 
         |lines[1 + 2*i + 1]| == n)) &&
    (forall lines, t, i :: 
        (lines == split_lines(s) && t == parse_int(lines[0]) && 0 <= i < t) ==> 
        (forall j :: 0 <= j < |lines[1 + 2*i + 1]| ==> 
         lines[1 + 2*i + 1][j] in "abcdefghijklmnopqrstuvwxyz"))
}

predicate ValidOutput(result: string)
{
    |result| >= 0 &&
    (result == "" || result[|result|-1] == '\n')
}

function transform_string(input_str: string, n: int, k: int): string
  requires 1 <= k <= n
  requires |input_str| == n
{
    var i := k - 1;
    if (n - i) % 2 == 0 then
        input_str[i..] + input_str[..i]
    else
        input_str[i..] + reverse_string(input_str[..i])
}

predicate is_lexicographically_optimal(result_str: string, input_str: string, n: int, k: int)
  requires |input_str| == n
{
    1 <= k <= n &&
    (exists transformation :: 
      transformation == transform_string(input_str, n, k) && result_str == transformation &&
      forall other_k :: 1 <= other_k <= n ==> 
        result_str <= transform_string(input_str, n, other_k))
}

// <vc-helpers>
// No helper lemmas required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var lines := split_lines(s);
  var t := parse_int(lines[0]);
  var result_acc := "";
  var caseIdx := 0;
  while caseIdx < t
    decreases t - caseIdx
    invariant 0 <= caseIdx <= t
    invariant lines == split_lines(s) && t == parse_int(lines[0])
    // from ValidInput we know lines has enough entries: |lines| >= 1 + 2*t
    invariant |lines| >= 1 + 2*t
  {
    var base := 1 + 2 * caseIdx;
    // show indexing is safe
    assert base + 1 < |lines|;
    var n := parse_int(lines[base]);
    var str := lines[base + 1];
    // by ValidInput for this i we have |lines[base+1]| == parse_int(lines[base]) == n
    assert lines == split_lines(s) && t == parse_int(lines[0]) && 0 <= caseIdx < t;
    assert |str| == n;

    // find lexicographically minimal transformation
    var k := 1;
    var best := transform_string(str, n, 1);
    k := 2;
    while k <= n
      decreases n - k + 1
    {
      var cand := transform_string(str, n, k);
      if cand < best {
        best := cand;
      }
      k := k + 1;
    }

    result_acc := result_acc + best + "\n";
    caseIdx := caseIdx + 1;
  }
  return result_acc;
}
// </vc-code>

