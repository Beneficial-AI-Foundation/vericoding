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
requires 0 <= k < n && n > 0
ensures rotate_segment(rotate_segment(seg, k, n), n - k, n) == seg
{
  var rotated1 := rotate_segment(seg, k, n);
  var rotated2 := rotate_segment(rotated1, n - k, n);
  
  // Simplified proof using modular arithmetic properties
  calc == {
    rotated2.0;
    var temp := (rotated1.0 + (n - k)) % n;
    if temp == 0 then n else temp;
    var temp1 := (seg.0 + k) % n;
    var norm1 := if temp1 == 0 then n else temp1;
    var temp2 := (norm1 + (n - k)) % n;
    if temp2 == 0 then n else temp2;
    // Since 1 <= seg.0 <= n, seg.0 + k < n + n = 2n
    // and seg.0 + k + (n - k) = seg.0 + n
    (seg.0 + n) % n;
    if seg.0 % n == 0 then n else seg.0 % n;
    seg.0;
  }
  calc == {
    rotated2.1;
    var temp := (rotated1.1 + (n - k)) % n;
    if temp == 0 then n else temp;
    var temp1 := (seg.1 + k) % n;
    var norm1 := if temp1 == 0 then n else temp1;
    var temp2 := (norm1 + (n - k)) % n;
    if temp2 == 0 then n else temp2;
    (seg.1 + n) % n;
    if seg.1 % n == 0 then n else seg.1 % n;
    seg.1;
  }
}

lemma rotate_segment_identity(seg: (int, int), n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires n > 0
ensures rotate_segment(seg, n, n) == seg
{
  var rotated := rotate_segment(seg, n, n);
  
  calc == {
    rotated.0;
    var a := (seg.0 + n) % n;
    if a == 0 then n else a;
    seg.0 % n;
    if seg.0 % n == 0 then n else seg.0 % n;
    seg.0;
  }
  calc == {
    rotated.1;
    var b := (seg.1 + n) % n;
    if b == 0 then n else b;
    seg.1 % n;
    if seg.1 % n == 0 then n else seg.1 % n;
    seg.1;
  }
}

lemma rotate_segment_composition(seg: (int, int), k1: int, k2: int, n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k1 >= 0 && k2 >= 0 && n > 0
ensures rotate_segment(rotate_segment(seg, k1, n), k2, n) == rotate_segment(seg, (k1 + k2) % n, n)
{
  var rotated1 := rotate_segment(seg, k1, n);
  var rotated2 := rotate_segment(rotated1, k2, n);
  var direct := rotate_segment(seg, (k1 + k2) % n, n);
  
  // Show equality by computing both sides
  calc == {
    rotated2.0;
    var a1 := (seg.0 + k1) % n; var norm_a1 := if a1 == 0 then n else a1;
    var a2 := (norm_a1 + k2) % n; var norm_a2 := if a2 == 0 then n else a2;
    norm_a2;
    (seg.0 + k1 + k2) % n;
    var temp := if ((seg.0 + k1 + k2) % n) == 0 then n else ((seg.0 + k1 + k2) % n);
    temp;
    direct.0;
  }
  calc == {
    rotated2.1;
    var b1 := (seg.1 + k1) % n; var norm_b1 := if b1 == 0 then n else b1;
    var b2 := (norm_b1 + k2) % n; var norm_b2 := if b2 == 0 then n else b2;
    norm_b2;
    (seg.1 + k1 + k2) % n;
    var temp := if ((seg.1 + k1 + k2) % n) == 0 then n else ((seg.1 + k1 + k2) % n);
    temp;
    direct.1;
  }
}

predicate check_symmetry(data: InputData, k: int)
{
  1 <= k < data.n &&
  (forall seg :: seg in data.segments ==> 
      rotate_segment(seg, k, data.n) in data.segments)
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
    invariant !possible ==> forall j :: 1 <= j < k ==> !check_symmetry(data, j)
  {
    if check_symmetry(data, k) {
      possible := true;
      break;
    }
    k := k + 1;
  }
  
  if possible {
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

