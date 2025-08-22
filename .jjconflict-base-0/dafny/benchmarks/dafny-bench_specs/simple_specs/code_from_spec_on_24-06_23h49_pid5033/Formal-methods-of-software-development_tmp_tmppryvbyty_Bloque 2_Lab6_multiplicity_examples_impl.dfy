//IMPL 

// MULTISETS

method multiplicity_examples<T> ()
{
    // Example 1: Create a multiset and check multiplicities
    var ms1 := multiset{1, 1, 2, 3, 3, 3};
    assert ms1[1] == 2;  // element 1 appears 2 times
    assert ms1[2] == 1;  // element 2 appears 1 time
    assert ms1[3] == 3;  // element 3 appears 3 times
    assert ms1[4] == 0;  // element 4 appears 0 times
    
    // Example 2: Empty multiset
    var ms2: multiset<int> := multiset{};
    assert ms2[1] == 0;  // any element has multiplicity 0 in empty multiset
    
    // Example 3: Single element multiset
    var ms3 := multiset{5};
    assert ms3[5] == 1;
    assert ms3[6] == 0;
    
    // Example 4: Multiset operations affecting multiplicity
    var ms4 := multiset{1, 2, 2};
    var ms5 := multiset{2, 3};
    var union := ms4 + ms5;  // multiset union
    assert union[1] == 1;    // 1 + 0 = 1
    assert union[2] == 3;    // 2 + 1 = 3
    assert union[3] == 1;    // 0 + 1 = 1
}