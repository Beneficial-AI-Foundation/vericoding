function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
lemma CalcBalNonNegative(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] in {0, 1}
    requires CalcBal(s, i, j) >= 0
    requires forall k :: i <= k < j ==> CalcBal(s, i, k) >= 0
    ensures forall k :: i <= k <= j ==> CalcBal(s, i, k) >= 0
{
    if i == j {
        return;
    }
    
    var balance_j := CalcBal(s, i, j);
    var balance_j_minus_1 := CalcBal(s, i, j - 1);
    
    assert balance_j_minus_1 >= 0;
    
    if s[j - 1] == 0 {
        assert balance_j == 1 + balance_j_minus_1;
    } else {
        assert s[j - 1] == 1;
        assert balance_j == -1 + balance_j_minus_1;
    }
}

lemma CalcBalNegativeExists(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires forall k :: i <= k < j ==> s[k] in {0, 1}
    requires CalcBal(s, i, j) < 0
    ensures exists k :: i <= k <= j && CalcBal(s, i, k) < 0
{
    assert CalcBal(s, i, j) < 0;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def correct_bracketing(brackets: str) -> Bool
brackets is a string of "<" and ">". return True if every opening bracket has a corresponding closing bracket, i.e., (each open bracket is properly closed)
*/
// </vc-description>

// <vc-spec>
method correct_bracketing(brackets: seq<int>) returns (result: bool)
    requires forall i :: 0 <= i < |brackets| ==> brackets[i] in {0, 1}
    ensures result <==> (CalcBal(brackets, 0, |brackets|) == 0 && 
                        forall k :: 0 <= k <= |brackets| ==> CalcBal(brackets, 0, k) >= 0)
// </vc-spec>
// <vc-code>
{
    var balance := 0;
    var i := 0;
    
    while i < |brackets|
        invariant 0 <= i <= |brackets|
        invariant balance == CalcBal(brackets, 0, i)
        invariant forall k :: 0 <= k <= i ==> CalcBal(brackets, 0, k) >= 0
    {
        if brackets[i] == 0 {
            balance := balance + 1;
        } else {
            balance := balance - 1;
            if balance < 0 {
                assert CalcBal(brackets, 0, i + 1) < 0;
                CalcBalNegativeExists(brackets, 0, i + 1);
                result := false;
                return;
            }
        }
        i := i + 1;
    }
    
    if balance == 0 {
        CalcBalNonNegative(brackets, 0, |brackets|);
        result := true;
    } else {
        assert CalcBal(brackets, 0, |brackets|) != 0;
        result := false;
    }
}
// </vc-code>
