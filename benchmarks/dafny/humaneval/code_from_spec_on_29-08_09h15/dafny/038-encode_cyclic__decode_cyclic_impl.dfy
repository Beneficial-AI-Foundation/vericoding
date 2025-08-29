method encode_cyclic(s: seq<int>) returns (res: seq<int>) 
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma mod3_cases(i: int)
    ensures i % 3 == 0 || i % 3 == 1 || i % 3 == 2
{}

lemma decode_encode_inverse_helper(s: seq<int>, i: int)
    requires 0 <= i < |s| - |s| % 3
    ensures i % 3 == 0 ==> (i + 2) % 3 == 2
    ensures i % 3 == 1 ==> (i - 1) % 3 == 0
    ensures i % 3 == 2 ==> (i - 2) % 3 == 1
{
    if i % 3 == 0 {
        assert (i + 2) % 3 == 2;
    } else if i % 3 == 1 {
        assert (i - 1) % 3 == 0;
    } else {
        assert i % 3 == 2;
        assert i >= 2;
        calc {
            (i - 2) % 3;
            == { assert i % 3 == 2; }
            (3 * (i / 3) + 2 - 2) % 3;
            == 
            (3 * (i / 3)) % 3;
            == 
            0 % 3;
            == 
            0;
        }
        calc {
            (i - 2) % 3;
            == 
            0;
            != 
            1;
        }
        assert i >= 2;
        if i == 2 {
            assert (i - 2) % 3 == 0 % 3 == 0;
            assert 0 != 1;
        } else {
            assert i >= 5;
            calc {
                (i - 2) % 3;
                == { assert i % 3 == 2; }
                ((i - 2) + 2) % 3 - 2 % 3;
                == 
                (i % 3) - (2 % 3);
                == 
                2 - 2;
                == 
                0;
            }
        }
        calc {
            (i - 2) % 3;
            == { assert i == 3 * (i / 3) + 2; }
            (3 * (i / 3) + 2 - 2) % 3;
            == 
            (3 * (i / 3)) % 3;
            == 
            0;
        }
        assert (i - 2) % 3 == 1 by {
            if i % 3 == 2 {
                var k := i / 3;
                assert i == 3 * k + 2;
                assert i - 2 == 3 * k;
                calc {
                    (i - 2) % 3;
                    == (3 * k) % 3;
                    == 0;
                }
                assert false;
            }
        }
    }
}

lemma index_bounds_helper(s: seq<int>, i: int)
    requires 0 <= i < |s| - |s| % 3
    ensures i % 3 == 0 ==> 0 <= i + 2 < |s|
    ensures i % 3 == 1 ==> 0 <= i - 1 < |s|
    ensures i % 3 == 2 ==> 0 <= i + 1 < |s|
{
    if i % 3 == 0 {
        assert i + 2 < |s| - |s| % 3 + 2;
        assert |s| % 3 >= 0 && |s| % 3 <= 2;
        assert i + 2 < |s| - |s| % 3 + 2 <= |s|;
    } else if i % 3 == 1 {
        assert i >= 1;
        assert i - 1 >= 0;
    } else {
        assert i % 3 == 2;
        assert i + 1 < |s| - |s| % 3 + 1;
        assert |s| % 3 >= 0;
        assert i + 1 <= |s| - |s| % 3 < |s|;
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method decode_cyclic(s: seq<int>) returns (res: seq<int>)
Decode data. Ensures: returns the correct size/count; the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)
    // post-conditions-start
    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    var arr := new int[|s|];
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant arr.Length == |s|
        invariant forall j :: |s| - |s| % 3 <= j < i ==> arr[j] == s[j]
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 0 ==> arr[j] == s[j + 2])
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 1 ==> arr[j] == s[j - 1])
        invariant forall j :: 0 <= j < i && j < |s| - |s| % 3 ==> (j % 3 == 2 ==> arr[j] == s[j + 1])
    {
        if i >= |s| - |s| % 3 {
            arr[i] := s[i];
        } else {
            mod3_cases(i);
            index_bounds_helper(s, i);
            if i % 3 == 0 {
                arr[i] := s[i + 2];
            } else if i % 3 == 1 {
                arr[i] := s[i - 1];
            } else {
                arr[i] := s[i + 1];
            }
        }
        i := i + 1;
    }
    
    res := arr[..];
}
// </vc-code>

