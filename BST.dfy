datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([2,7,3,8,4,-2,9,0]);
	PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree)
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(l);
			print n;
			print "\n";
			PrintTreeNumbersInorder(r);
	}
}

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
decreases t
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
    {
        var i, t0 := Init(q);

        i, t := BuildBST_Iterate(q, i, t0);
        StrengthenPost_BuildBST_Iterate(q, i, t);
    }

method Init (q : seq<int>) returns (i : nat, t : Tree)
    requires NoDuplicates(q)
    ensures BuildBST_Invariant(q, i, t)
    {

        // Assignment
        assert(BuildBST_Invariant(q, 0, Empty));
        i, t := 0, Empty;
    }

lemma StrengthenPost_BuildBST_Iterate(q : seq<int>, i: nat, t: Tree)
    requires i >= |q| && BuildBST_Invariant(q, i, t);
    ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{

}

method BuildBST_Iterate(q: seq<int>, i0 :nat, t0: Tree) returns (i: nat, t:Tree)
    requires NoDuplicates(q)
    requires BuildBST_Invariant(q, i0, t0)
    ensures i >= |q| && BuildBST_Invariant(q, i, t);
{
    i := i0;
    t := t0;
        
    // Iterate
    while i < |q|
        invariant BuildBST_Invariant(q, i, t)
        decreases |q| - i
        {
            i, t := InesrtionLoopBody(q, i, t);
        }
    
}

method InesrtionLoopBody(q : seq<int>, i0 : nat, t0: Tree) returns (i : nat, t: Tree)
    requires NoDuplicates(q)
    requires BuildBST_Invariant(q, i0, t0)
    ensures BuildBST_Invariant(q, i, t)
    requires i0 < |q|
    ensures i > i0
    {
        t := InsertBST(t0, q[i0]);

        // Assignment
        LemmaInsertionLoopBody(q, t0, t, i0);
        i := i0 + 1;

    }

lemma LemmaInsertionLoopBody(q : seq<int>, t0: Tree, t:Tree, i0 : nat)
    requires NoDuplicates(q)
    requires BuildBST_Invariant(q, i0, t0)
    requires i0 < |q|
    requires BST(t)
    requires NumbersInTree(t) == NumbersInTree(t0)+{q[i0]}
    ensures BuildBST_Invariant(q, i0 + 1, t)
{
}


predicate BuildBST_Invariant(q: seq<int>, i : nat, t: Tree)
{
    i <= |q| &&
    NumbersInTree(t) == NumbersInSequence(q[..i]) &&
    BST(t)
}
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
    decreases |Inorder(t0)|, 4
    {
        match t0 {
		case Empty => t := Node(x, Empty, Empty);
		case Node(y ,left,right) => t := InsertBST_NonEmpty(y, left, right, x);
	    }
    }

method InsertBST_NonEmpty(y:int, left0:Tree, right0:Tree, x: int) returns (t: Tree)
	requires BST(Node(y, left0, right0)) && x !in NumbersInTree(Node(y, left0, right0))
    ensures BST(t) 
    ensures NumbersInTree(t) == NumbersInTree(Node(y, left0, right0))+{x}
    decreases |Inorder(Node(y, left0, right0))|, 3
    {
        // Weaken precondition

        LemmaBinarySearchSubtree(y, left0, right0);
        RootGreaterThanLeftSubtree(y, left0, right0);
        RootLesserThanRightSubtree(y, left0, right0);

       t := InsertBST_NonEmptyb(y, left0, right0, x);
    }

method InsertBST_NonEmptyb(y:int, left0:Tree, right0:Tree, x: int) returns (t: Tree)
	requires BST(Node(y, left0, right0)) && x !in NumbersInTree(Node(y, left0, right0))
    requires BST(left0) && BST(right0)
    requires forall i :: i in NumbersInTree(right0) ==> i > y
    requires forall i :: i in NumbersInTree(left0) ==> i < y

    ensures BST(t) 
    ensures NumbersInTree(t) == NumbersInTree(Node(y, left0, right0))+{x}
    decreases |Inorder(Node(y, left0, right0))|, 2
    {
        var left, right := InsertToSubtree(y, left0, right0, x);

        LemmaInsertNonempty(y, left, right);
        t := Node(y, left, right);
    }

lemma LemmaInsertNonempty(y: int, left:Tree, right:Tree)
    requires BST(left) && BST(right)
    requires Ascending(Inorder(Node(y, left, right)))
    
    ensures BST(Node(y, left, right))
{

}

method InsertToSubtree(y:int, left0:Tree, right0:Tree, x: int) returns (left: Tree, right: Tree)
	requires BST(Node(y, left0, right0)) && x !in NumbersInTree(Node(y, left0, right0))
    requires BST(left0) && BST(right0)
    requires forall i :: i in NumbersInTree(right0) ==> i > y
    requires forall i :: i in NumbersInTree(left0) ==> i < y

    ensures BST(right) && BST(left)
    ensures NumbersInTree(Node(y, left0, right0))+{x}
         == NumbersInTree(left) + NumbersInTree(right) + {y}
    ensures Ascending(Inorder(Node(y, left, right)))

    decreases |Inorder(Node(y, left0, right0))|, 1
{
    if (x > y)
        {
            left, right := InsertToRightSubtree(y, left0, right0, x);
        }
        else
        {
            left, right := InsertToLeftSubtree(y, left0, right0, x);
        }
}

method InsertToRightSubtree(y:int, left0:Tree, right0:Tree, x: int) returns (left: Tree, right: Tree)
	requires BST(Node(y, left0, right0)) && x !in NumbersInTree(Node(y, left0, right0))
    requires BST(left0) && BST(right0)
    requires forall i :: i in NumbersInTree(right0) ==> i > y
    requires forall i :: i in NumbersInTree(left0) ==> i < y
    requires x > y

    ensures BST(right) && BST(left)
    ensures NumbersInTree(Node(y, left0, right0))+{x}
         == NumbersInTree(left) + NumbersInTree(right) + {y}
    ensures Ascending(Inorder(Node(y, left, right)))

    decreases |Inorder(Node(y, left0, right0))|, 0
    {
        right := InsertBST(right0, x);
        LemmaJoinTrees(y, left0, right);

        left := left0; 
    }

method InsertToLeftSubtree(y:int, left0:Tree, right0:Tree, x: int) returns (left: Tree, right: Tree)
	requires BST(Node(y, left0, right0)) && x !in NumbersInTree(Node(y, left0, right0))
    requires BST(left0) && BST(right0)
    requires forall i :: i in NumbersInTree(right0) ==> i > y
    requires forall i :: i in NumbersInTree(left0) ==> i < y
    requires x < y

    ensures BST(right) && BST(left)
    ensures NumbersInTree(Node(y, left0, right0))+{x}
         == NumbersInTree(left) + NumbersInTree(right) + {y}
    ensures Ascending(Inorder(Node(y, left, right)))

    decreases |Inorder(Node(y, left0, right0))|, 0
    {
        left := InsertBST(left0, x);
        LemmaJoinTrees(y, left, right0);

        right := right0; 
    }

lemma {:verify true} LemmaJoinTrees(n : int, left:Tree, right:Tree)
    requires BST(left)
    requires BST(right)
    requires forall x :: x in NumbersInTree(left) ==> x < n
    requires forall x :: x in NumbersInTree(right) ==> x > n

    ensures Ascending(Inorder(left) + [n] + Inorder(right))
{
    ghost var leftarr, rightarr := Inorder(left), Inorder(right);

    assert(Ascending(leftarr));
    assert(forall i :: 0 <= i < |leftarr| ==> leftarr[i] in NumbersInTree(left));
    assert(forall i :: 0 <= i < |leftarr| ==> leftarr[i] < n);
    assert(Ascending(leftarr + [n]));

    assert(Ascending(rightarr));
    assert(forall i :: 0 <= i < |rightarr| ==> rightarr[i] in NumbersInTree(right));

    assert(Ascending(leftarr + [n] + rightarr));
}

lemma {:verify true} RootLesserThanRightSubtree(root : int, left:Tree, right:Tree)
    requires BST(Node(root, left, right))
    ensures forall i :: i in NumbersInTree(right) ==> i > root
{
    ghost var leftseq, rightseq :=  Inorder(left), Inorder(right);
    ghost var all := leftseq + [root] + rightseq;
    ghost var rightAndRoot := [root] + rightseq;

    assert(Ascending(all));
    LemmaAscendingSubsequence(all, rightAndRoot, |leftseq|);
    assert(Ascending(rightAndRoot));

    assert(rightAndRoot[0] == root);
    assert (forall i,j :: 0 <= i < j < |rightAndRoot| ==> rightAndRoot[i] < rightAndRoot[j]);
    assert (forall j :: 0 < j < |rightAndRoot| ==> root < rightAndRoot[j]);
    assert (rightAndRoot[1..] == rightseq);
}

lemma{:verify true} RootGreaterThanLeftSubtree(root : int, left:Tree, right:Tree)
    requires BST(Node(root, left, right))
    ensures forall i :: i in NumbersInTree(left) ==> i < root

{
    ghost var leftseq, rightseq :=  Inorder(left), Inorder(right);
    ghost var all := leftseq + [root] + rightseq;
    ghost var leftAndRoot := leftseq + [root];

    assert(Ascending(all));
    LemmaAscendingSubsequence(all, leftAndRoot, 0);
    assert(Ascending(leftAndRoot));

    assert(leftAndRoot[|leftAndRoot| - 1] == root);
    assert (forall i,j :: 0 <= i < j < |leftAndRoot| ==> leftAndRoot[i] < leftAndRoot[j]);
    assert (forall i :: 0 <= i < |leftAndRoot| - 1 ==> root > leftAndRoot[i]);
    assert (leftAndRoot[..|leftseq|] == leftseq);

}

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	assert Ascending(Inorder(Node(n, left, right)));
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
	assert q == Inorder(Node(n, left, right));
	assert Ascending(qleft+[n]+qright);
	assert Ascending(qleft) by { LemmaAscendingSubsequence(q, qleft, 0); }
	assert Ascending(qright) by { LemmaAscendingSubsequence(q, qright, |qleft|+1); }
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}
