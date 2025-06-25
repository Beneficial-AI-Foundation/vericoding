// ATOM 
pub fn BinarySearch(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    ensures(r < 0 ==> forall|i: nat| i < intSeq.len() ==> intSeq[i] != key)
{
}

// ATOM 
spec fn BinarySearchTransition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    && (r < 0 ==> forall|i: nat| i < intSeq.len() ==> intSeq[i] != key)
}

// ATOM 
pub fn BinarySearchDeterministic(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    ensures(r < 0 ==> forall|i: nat| i < intSeq.len() ==> intSeq[i] != key)
    ensures(r < 0 ==> r == -1)
    ensures(r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
{
}

// ATOM 
spec fn BinarySearchDeterministicTransition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    && (r < 0 ==> forall|i: nat| i < intSeq.len() ==> intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
}

// ATOM 
pub fn BinarySearchWrong1(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    ensures(r < 0 ==> forall|i: nat| 0 < i < intSeq.len() ==> intSeq[i] != key)
    ensures(r < 0 ==> r == -1)
    ensures(r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
{
}

// ATOM 
spec fn BinarySearchWrong1Transition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    && (r < 0 ==> forall|i: nat| 0 < i < intSeq.len() ==> intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
}

// ATOM 
pub fn BinarySearchWrong2(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    ensures(r < 0 ==> forall|i: nat| 0 <= i < intSeq.len() - 1 ==> intSeq[i] != key)
    ensures(r < 0 ==> r == -1)
    ensures(r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
{
}

// ATOM 
spec fn BinarySearchWrong2Transition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < intSeq.len() && intSeq[r] == key)
    && (r < 0 ==> forall|i: nat| 0 <= i < intSeq.len() - 1 ==> intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall|i: nat| i < r ==> intSeq[i] < key)
}

// ATOM 
pub fn BinarySearchWrong3(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(r < 0 || (r < intSeq.len() && intSeq[r] == key))
{
}

// ATOM 
spec fn BinarySearchWrong3Transition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    r < 0 || (r < intSeq.len() && intSeq[r] == key)
}

// ATOM 
pub fn BinarySearchWrong4(intSeq: Seq<int>, key: int) -> (r: int)
    requires(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
    ensures(0 <= r < intSeq.len() && intSeq[r] == key)
{
}

// ATOM 
spec fn BinarySearchWrong4Transition(intSeq: Seq<int>, key: int, r: int) -> bool
    recommends(forall|i: int, j: int| 0 <= i <= j < intSeq.len() ==> intSeq[i] <= intSeq[j])
{
    0 <= r < intSeq.len() && intSeq[r] == key
}