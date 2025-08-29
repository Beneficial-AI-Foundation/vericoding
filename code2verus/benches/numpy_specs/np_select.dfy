//SPEC
method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length > 0 && choicelist.Length > 0
    requires condlist.Length == choicelist.Length 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && choicelist[i].Length == condlist[0].Length
    ensures ret.Length == condlist[0].Length
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist[0].Length ==>  condlist[i][j] ==> ret[j] == choicelist[i][j]
{}