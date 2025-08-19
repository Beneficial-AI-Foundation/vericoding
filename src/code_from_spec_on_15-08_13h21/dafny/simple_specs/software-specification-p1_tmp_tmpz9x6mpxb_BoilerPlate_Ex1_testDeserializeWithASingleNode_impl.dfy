datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)


//ATOM

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)


//ATOM

// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
 requires |codes| > 0 || |trees| > 0
 ensures |deserialiseAux(codes, trees)| >= 0
{
 if |codes| == 0 then trees
 else
  match codes[0] {
   case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
   case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
   case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
  }
}


//ATOM

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
 requires |s| > 0
{
 deserialiseAux(s, [])
}


//IMPL testDeserializeWithASingleNode

/* code modified by LLM (iteration 1): Added lemma to prove properties of deserialise function for the specific test case */
lemma DeserialiseClf1CSnd2()
    ensures deserialise([CLf(1), CSNd(2)]) == [SingleNode(2, Leaf(1))]
    ensures |deserialise([CLf(1), CSNd(2)])| == 1
{
    var codes := [CLf(1), CSNd(2)];
    
    // Step 1: deserialise calls deserialiseAux with empty trees
    assert deserialise(codes) == deserialiseAux(codes, []);
    
    // Step 2: First iteration - process CLf(1)
    assert codes[0] == CLf(1);
    assert codes[1..] == [CSNd(2)];
    assert deserialiseAux(codes, []) == deserialiseAux([CSNd(2)], [] + [Leaf(1)]);
    assert [] + [Leaf(1)] == [Leaf(1)];
    assert deserialiseAux(codes, []) == deserialiseAux([CSNd(2)], [Leaf(1)]);
    
    // Step 3: Second iteration - process CSNd(2)
    var intermediate_trees := [Leaf(1)];
    assert |intermediate_trees| == 1;
    assert intermediate_trees[|intermediate_trees|-1] == Leaf(1);
    assert intermediate_trees[..|intermediate_trees|-1] == [];
    assert deserialiseAux([CSNd(2)], intermediate_trees) == 
           deserialiseAux([], [] + [SingleNode(2, Leaf(1))]);
    assert [] + [SingleNode(2, Leaf(1))] == [SingleNode(2, Leaf(1))];
    
    // Step 4: Final step - empty codes
    assert deserialiseAux([], [SingleNode(2, Leaf(1))]) == [SingleNode(2, Leaf(1))];
}

method testDeserializeWithASingleNode()
{
    var codes := [CLf(1), CSNd(2)];
    var result := deserialise(codes);
    
    /* code modified by LLM (iteration 1): Added lemma call to prove the assertions */
    DeserialiseClf1CSnd2();
    
    assert |result| == 1;
    assert result[0] == SingleNode(2, Leaf(1));
}