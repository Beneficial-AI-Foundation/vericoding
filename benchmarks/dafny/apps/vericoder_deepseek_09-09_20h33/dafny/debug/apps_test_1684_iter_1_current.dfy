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
lemma rotate_segment_symmetric(seg: (int, int), k: int, n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
ensures rotate_segment(rotate_segment(seg, k, n), n - k, n) == seg
{
}

lemma rotate_segment_identity(seg: (int, int), n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires n > 0
ensures rotate_segment(seg, n, n) == seg
{
}

lemma rotate_segment_composition(seg: (int, int), k1: int, k2: int, n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k1 >= 0 && k2 >= 0 && n > 0
ensures rotate_segment(rotate_segment(seg, k1, n), k2, n) == rotate_segment(seg, (k1 + k2) % n, n)
{
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
  var data := parse_input(stdin_input);
  var n := data.n;
  var segments := data.segments;
  
  if n == 1 {
    return "Yes";
  }
  
  var possible := false;
  var k := 1;
  while k < n
    invariant 1 <= k <= n
    invariant !possible ==> forall j :: 1 <= j < k ==> !(n % j == 0 && check_symmetry(data, j))
    invariant possible ==> exists j :: 1 <= j < k && n % j == 0 && check_symmetry(data, j)
  {
    if n % k == 0 {
      if check_symmetry(data, k) {
        possible := true;
        break;
      }
    }
    k := k + 1;
  }
  
  if possible {
    return "Yes";
  } else {
    return "No";
  }
}

function check_symmetry(data: InputData, k: int): bool
requires 1 <= k < data.n && data.n % k == 0
{
  forall seg :: seg in data.segments ==> 
    seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
    rotate_segment(seg, k, data.n) in data.segments
}
// </vc-code>

