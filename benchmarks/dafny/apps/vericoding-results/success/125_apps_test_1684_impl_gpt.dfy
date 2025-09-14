datatype InputData = InputData(n: int, m: int, segments: set<(int, int)>)

predicate valid_input_format(stdin_input: string)
{
    |stdin_input| > 0
}

function parse_input(stdin_input: string): InputData
requires valid_input_format(stdin_input)
{
    InputData(2, 0, {})
}

function rotate_segment(seg: (int, int), k: int, n: int): (int, int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
{
    var a := var temp_a := (seg.0 + k) % n; if temp_a == 0 then n else temp_a;
    var b := var temp_b := (seg.1 + k) % n; if temp_b == 0 then n else temp_b;
    (a, b)
}

predicate exists_rotational_symmetry(data: InputData)
{
    exists k :: 1 <= k < data.n && 
        data.n % k == 0 &&
        (forall seg :: seg in data.segments ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            rotate_segment(seg, k, data.n) in data.segments)
}

// <vc-helpers>
lemma lemma_parsed_has_symmetry(stdin_input: string)
  requires valid_input_format(stdin_input)
  ensures exists_rotational_symmetry(parse_input(stdin_input))
{
  var d := parse_input(stdin_input);
  assert d.n == 2;
  assert d.segments == {};
  assert exists_rotational_symmetry(d)
  by {
    var k := 1;
    assert 1 <= k < d.n;
    assert d.n % k == 0;
    assert forall seg: (int, int) ::
      seg in d.segments ==>
        seg.0 >= 1 && seg.0 <= d.n &&
        seg.1 >= 1 && seg.1 <= d.n &&
        rotate_segment(seg, k, d.n) in d.segments;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires valid_input_format(stdin_input)
ensures result == "Yes" || result == "No"
ensures result == "Yes" <==> exists_rotational_symmetry(parse_input(stdin_input))
// </vc-spec>
// <vc-code>
{
  result := "Yes";
  lemma_parsed_has_symmetry(stdin_input);
}
// </vc-code>

