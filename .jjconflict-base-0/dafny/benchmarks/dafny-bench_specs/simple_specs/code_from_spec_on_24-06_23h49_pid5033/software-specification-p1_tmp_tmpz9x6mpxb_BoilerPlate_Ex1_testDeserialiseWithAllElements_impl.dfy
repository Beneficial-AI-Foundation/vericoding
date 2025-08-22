//ATOM
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

//IMPL testDeserialiseWithAllElements

/* code modified by LLM (iteration 1): Added helper lemma to prove the specific case */
lemma DeserialiseSpecificCase()
    ensures deserialise([CLf(1), CLf(2), CSNd(3), CDNd(4)]) == [DoubleNode(4, SingleNode(3, Leaf(2)), Leaf(1))]
    ensures |deserialise([CLf(1), CLf(2), CSNd(3), CDNd(4)])| == 1
{
    var codes := [CLf(1), CLf(2), CSNd(3), CDNd(4)];
    
    // Step by step calculation of deserialiseAux
    calc {
        deserialise(codes);
        deserialiseAux(codes, []);
        deserialiseAux([CLf(2), CSNd(3), CDNd(4)], [Leaf(1)]);
        deserialiseAux([CSNd(3), CDNd(4)], [Leaf(1), Leaf(2)]);
        deserialiseAux([CDNd(4)], [Leaf(1), SingleNode(3, Leaf(2))]);
        deserialiseAux([], [DoubleNode(4, SingleNode(3, Leaf(2)), Leaf(1))]);
        [DoubleNode(4, SingleNode(3, Leaf(2)), Leaf(1))];
    }
}

method testDeserialiseWithAllElements()
{
    var codes := [CLf(1), CLf(2), CSNd(3), CDNd(4)];
    var result := deserialise(codes);
    
    /* code modified by LLM (iteration 1): Added lemma call and simplified assertion */
    DeserialiseSpecificCase();
    
    assert |result| == 1;
}