predicate ValidInput(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>)
{
    |attacking_powers| == s && |bases| == b
}

function SumGoldForSpaceship(attacking_power: nat, bases: seq<(nat, nat)>): nat
{
    if |bases| == 0 then 0
    else if attacking_power >= bases[0].0 then bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..])
    else SumGoldForSpaceship(attacking_power, bases[1..])
}

predicate ValidOutput(s: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>, result: seq<nat>)
{
    |result| == s &&
    (forall i :: 0 <= i < s ==> result[i] >= 0) &&
    (forall i :: 0 <= i < s && i < |attacking_powers| ==> result[i] == SumGoldForSpaceship(attacking_powers[i], bases))
}

// <vc-helpers>
lemma SumGoldForSpaceshipCorrectness(attacking_power: nat, bases: seq<(nat, nat)>, i: nat)
    requires 0 <= i <= |bases|
    ensures SumGoldForSpaceship(attacking_power, bases[i..]) >= 0
    decreases |bases| - i
{
    if i == |bases| {
        assert bases[i..] == [];
    } else {
        SumGoldForSpaceshipCorrectness(attacking_power, bases, i + 1);
    }
}

lemma SliceRelationship(bases: seq<(nat, nat)>, i: nat)
    requires 0 < i < |bases|
    ensures bases[1..][..i] == bases[1..i+1]
{
    // This lemma establishes that taking first i elements of bases[1..]
    // is the same as bases[1..i+1]
}

lemma SumGoldForSpaceshipAppend(attacking_power: nat, bases: seq<(nat, nat)>, i: nat)
    requires 0 <= i < |bases|
    ensures SumGoldForSpaceship(attacking_power, bases[..i+1]) == 
            SumGoldForSpaceship(attacking_power, bases[..i]) + 
            (if attacking_power >= bases[i].0 then bases[i].1 else 0)
{
    if i == 0 {
        assert bases[..1] == [bases[0]];
        assert bases[..0] == [];
        assert SumGoldForSpaceship(attacking_power, bases[..0]) == 0;
        assert SumGoldForSpaceship(attacking_power, bases[..1]) == SumGoldForSpaceship(attacking_power, [bases[0]]);
        if attacking_power >= bases[0].0 {
            assert SumGoldForSpaceship(attacking_power, [bases[0]]) == bases[0].1;
        } else {
            assert SumGoldForSpaceship(attacking_power, [bases[0]]) == 0;
        }
    } else {
        assert bases[..i+1][0] == bases[0];
        assert bases[..i+1][1..] == bases[1..i+1];
        
        if attacking_power >= bases[0].0 {
            calc {
                SumGoldForSpaceship(attacking_power, bases[..i+1]);
                == bases[0].1 + SumGoldForSpaceship(attacking_power, bases[..i+1][1..]);
                == bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..i+1]);
            }
            
            calc {
                SumGoldForSpaceship(attacking_power, bases[..i]);
                == { if i > 1 { assert bases[..i][0] == bases[0]; assert bases[..i][1..] == bases[1..i]; } }
                bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..i]);
            }
            
            SumGoldForSpaceshipAppend(attacking_power, bases[1..], i-1);
            assert bases[1..][..i-1] == bases[1..i];
            assert bases[1..][i-1] == bases[i];
            
            // Key: establish the slice relationship
            SliceRelationship(bases, i);
            assert bases[1..][..i] == bases[1..i+1];
            
            calc {
                SumGoldForSpaceship(attacking_power, bases[1..i+1]);
                == { assert bases[1..][..i] == bases[1..i+1]; }
                SumGoldForSpaceship(attacking_power, bases[1..][..i]);
                == SumGoldForSpaceship(attacking_power, bases[1..][..i-1]) + (if attacking_power >= bases[i].0 then bases[i].1 else 0);
                == { assert bases[1..][..i-1] == bases[1..i]; }
                SumGoldForSpaceship(attacking_power, bases[1..i]) + (if attacking_power >= bases[i].0 then bases[i].1 else 0);
            }
        } else {
            calc {
                SumGoldForSpaceship(attacking_power, bases[..i+1]);
                == SumGoldForSpaceship(attacking_power, bases[..i+1][1..]);
                == SumGoldForSpaceship(attacking_power, bases[1..i+1]);
            }
            
            calc {
                SumGoldForSpaceship(attacking_power, bases[..i]);
                == { if i > 1 { assert bases[..i][0] == bases[0]; assert bases[..i][1..] == bases[1..i]; } }
                SumGoldForSpaceship(attacking_power, bases[1..i]);
            }
            
            SumGoldForSpaceshipAppend(attacking_power, bases[1..], i-1);
            assert bases[1..][..i-1] == bases[1..i];
            assert bases[1..][i-1] == bases[i];
            
            // Key: establish the slice relationship
            SliceRelationship(bases, i);
            assert bases[1..][..i] == bases[1..i+1];
            
            calc {
                SumGoldForSpaceship(attacking_power, bases[1..i+1]);
                == { assert bases[1..][..i] == bases[1..i+1]; }
                SumGoldForSpaceship(attacking_power, bases[1..][..i]);
                == SumGoldForSpaceship(attacking_power, bases[1..][..i-1]) + (if attacking_power >= bases[i].0 then bases[i].1 else 0);
                == { assert bases[1..][..i-1] == bases[1..i]; }
                SumGoldForSpaceship(attacking_power, bases[1..i]) + (if attacking_power >= bases[i].0 then bases[i].1 else 0);
            }
        }
    }
}

method ComputeGoldForSpaceship(attacking_power: nat, bases: seq<(nat, nat)>) returns (gold: nat)
    ensures gold == SumGoldForSpaceship(attacking_power, bases)
{
    gold := 0;
    var i := 0;
    
    while i < |bases|
        invariant 0 <= i <= |bases|
        invariant gold == SumGoldForSpaceship(attacking_power, bases[..i])
    {
        SumGoldForSpaceshipAppend(attacking_power, bases, i);
        if attacking_power >= bases[i].0 {
            gold := gold + bases[i].1;
        }
        i := i + 1;
    }
    
    assert bases[..i] == bases;
}
// </vc-helpers>

// <vc-spec>
method solve(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>) returns (result: seq<nat>)
    requires ValidInput(s, b, attacking_powers, bases)
    ensures ValidOutput(s, attacking_powers, bases, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < s
        invariant 0 <= i <= s
        invariant |result| == i
        invariant |attacking_powers| == s
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
        invariant forall j :: 0 <= j < i ==> result[j] == SumGoldForSpaceship(attacking_powers[j], bases)
    {
        var gold := ComputeGoldForSpaceship(attacking_powers[i], bases);
        result := result + [gold];
        i := i + 1;
    }
}
// </vc-code>

