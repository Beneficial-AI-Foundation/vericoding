function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
function CalcBalNoAcc(s: seq<int>, i: int, j: int) : int
    requires 0 <= i <= j <= |s|
    ensures CalcBalNoAcc(s, i, j) == CalcBal(s, i, j, 0)
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBalNoAcc(s, i, j - 1)
}

lemma lemma_CalcBal_acc_zero(s: seq<int>, i: int, j: int, acc: int)
    requires 0 <= i <= j <= |s|
    ensures CalcBal(s, i, j, acc) == CalcBal(s, i, j, 0) + acc
{
    if i == j then
        assert CalcBal(s, i, j, acc) == acc;
        assert CalcBal(s, i, j, 0) == 0;
        assert acc == 0 + acc;
    else
        lemma_CalcBal_acc_zero(s, i, j - 1, acc);
}

lemma lemma_CalcBal_by_prefix(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures CalcBal(s, i, j, 0) == CalcBal(s, 0, j, 0) - CalcBal(s, 0, i, 0)
{
    if i == j then
        assert CalcBal(s, i, j, 0) == 0;
        assert CalcBal(s, 0, j, 0) - CalcBal(s, 0, i, 0) == 0;
    else if i == 0 then
        assert CalcBal(s, i, j, 0) == CalcBal(s, 0, j, 0);
        assert CalcBal(s, 0, j, 0) - CalcBal(s, 0, i, 0) == CalcBal(s, 0, j, 0);
    else
        lemma_CalcBal_by_prefix(s, i, j - 1);
        lemma_CalcBal_by_prefix(s, 0, j - 1);
        CalcBal(s, i, j, 0); // Trigger calculation for (i, j)
        CalcBal(s, 0, j, 0); // Trigger calculation for (0, j)
        CalcBal(s, 0, i, 0); // Trigger calculation for (0, i)
        assert CalcBal(s, i, j, 0) == (if s[j-1] == 0 then 1 else -1) + CalcBal(s, i, j-1, 0);
        assert CalcBal(s, 0, j, 0) == (if s[j-1] == 0 then 1 else -1) + CalcBal(s, 0, j-1, 0);
        assert CalcBal(s, i, j, 0) == CalcBal(s, 0, j, 0) - CalcBal(s, 0, i, 0);
}
// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 
    // pre-conditions-start
    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var s1_prefix_min_bal := 0;
    var s1_current_bal := 0;
    var i := 0;
    while i <= |s1|
        invariant 0 <= i <= |s1|
        invariant s1_current_bal == CalcBal(s1, 0, i, 0)
        invariant (exists k :: 0 <= k <= i && s1_prefix_min_bal == CalcBal(s1, 0, k, 0)) || (i == 0 && s1_prefix_min_bal == 0)
        invariant forall k :: 0 <= k <= i ==> CalcBal(s1, 0, k, 0) >= s1_prefix_min_bal
    {
        if s1_current_bal < s1_prefix_min_bal then
            s1_prefix_min_bal := s1_current_bal;
        
        if i == |s1| { break; }
        
        i := i + 1;
        if i > 0 { // This implicitly covers i <= |s1| as it's the loop invariant for i
            s1_current_bal := s1_current_bal + (if s1[i-1] == 0 then 1 else -1);
            lemma_CalcBal_acc_zero(s1, 0, i, 0);
            lemma_CalcBal_acc_zero(s1, 0, i-1, 0);
            assert CalcBal(s1, 0, i, 0) == CalcBal(s1, 0, i-1, 0) + (if s1[i-1] == 0 then 1 else -1);
            assert CalcBal(s1, 0, i, 0) == s1_current_bal;
        } else { // i == 0
            s1_current_bal := 0;
             lemma_CalcBal_acc_zero(s1, 0, 0, 0);
            assert CalcBal(s1, 0, 0, 0) == s1_current_bal;
        }
    }

    if s1_prefix_min_bal < 0 then
        return false;

    var s2_current_acc_bal := CalcBal(s1, 0, |s1|, 0);
    var s2_prefix_min_bal := s2_current_acc_bal;
    var j := 0;
    while j <= |s2|
        invariant 0 <= j <= |s2|
        invariant s2_current_acc_bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0)
        invariant (exists k :: 0 <= k <= j && s2_prefix_min_bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0)) || (j == 0 && s2_prefix_min_bal == CalcBal(s1, 0, |s1|, 0))
        invariant forall k :: 0 <= k <= j ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0) >= s2_prefix_min_bal
    {
        if s2_current_acc_bal < s2_prefix_min_bal then
            s2_prefix_min_bal := s2_current_acc_bal;
        
        if j == |s2| { break; }
        
        j := j + 1;
        if j > 0 { // This implicitly covers j <= |s2| as it's the loop invariant for j
            s2_current_acc_bal := s2_current_acc_bal + (if s2[j-1] == 0 then 1 else -1);
            lemma_CalcBal_acc_zero(s2, 0, j, 0);
            lemma_CalcBal_acc_zero(s2, 0, j-1, 0);
            assert CalcBal(s2, 0, j, 0) == CalcBal(s2, 0, j-1, 0) + (if s2[j-1] == 0 then 1 else -1);
            assert s2_current_acc_bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0);
        } else { // j == 0
            lemma_CalcBal_acc_zero(s2, 0, 0, 0);
            s2_current_acc_bal := CalcBal(s1, 0, |s1|, 0);
            assert s2_current_acc_bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, j, 0);
        }
    }
    
    return s2_prefix_min_bal >= 0;
}
// </vc-code>

