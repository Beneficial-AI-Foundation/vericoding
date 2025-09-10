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
// Helper to check if all rotated segments are in the original set
predicate all_rotated_segments_in_set(segments: set<(int, int)>, k: int, n: int)
requires k >= 0 && n > 0
{
    forall seg :: seg in segments ==> 
        seg.0 >= 1 && seg.0 <= n && seg.1 >= 1 && seg.1 <= n &&
        rotate_segment(seg, k, n) in segments
}

// Helper method to check rotational symmetry for a specific k
method check_rotation_for_k(data: InputData, k: int) returns (is_symmetric: bool)
requires 1 <= k < data.n
requires data.n % k == 0
ensures is_symmetric <==> all_rotated_segments_in_set(data.segments, k, data.n)
{
    is_symmetric := true;
    
    // Check each segment
    var segments_seq := data.segments;
    
    // Iterate through all segments
    ghost var checked_segments: set<(int, int)> := {};
    
    while checked_segments != data.segments
        invariant checked_segments <= data.segments
        invariant is_symmetric <==> (forall seg :: seg in checked_segments ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            rotate_segment(seg, k, data.n) in data.segments)
        decreases data.segments - checked_segments
    {
        // Pick an unchecked segment
        var seg :| seg in data.segments && seg !in checked_segments;
        
        // Check bounds
        if seg.0 < 1 || seg.0 > data.n || seg.1 < 1 || seg.1 > data.n {
            is_symmetric := false;
            return;
        }
        
        // Check if rotated segment is in the set
        var rotated := rotate_segment(seg, k, data.n);
        if rotated !in data.segments {
            is_symmetric := false;
            return;
        }
        
        checked_segments := checked_segments + {seg};
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
    var data := parse_input(stdin_input);
    
    if data.n <= 1 {
        return "No";
    }
    
    // Check for each valid k (divisors of n from 1 to n-1)
    var k := 1;
    while k < data.n
        invariant 1 <= k <= data.n
        invariant !exists j :: 1 <= j < k && data.n % j == 0 && 
            all_rotated_segments_in_set(data.segments, j, data.n)
    {
        if data.n % k == 0 {
            var is_symmetric := check_rotation_for_k(data, k);
            if is_symmetric {
                assert all_rotated_segments_in_set(data.segments, k, data.n);
                assert exists j :: 1 <= j < data.n && data.n % j == 0 && 
                    all_rotated_segments_in_set(data.segments, j, data.n);
                assert exists_rotational_symmetry(data);
                return "Yes";
            }
        }
        k := k + 1;
    }
    
    assert !exists j :: 1 <= j < data.n && data.n % j == 0 && 
        all_rotated_segments_in_set(data.segments, j, data.n);
    assert !exists_rotational_symmetry(data);
    return "No";
}
// </vc-code>

