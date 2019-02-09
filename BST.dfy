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
        t := Empty;
        var i := 0;

        while i < |q|
            invariant i <= |q|
            invariant NumbersInTree(t) == NumbersInSequence(q[..i])
            invariant BST(t)
            decreases |q| - i
        {
            t := InsertBST(t, q[i]);
            i := i + 1;
        }
    }



method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
    decreases |Inorder(t0)|, 1
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
    decreases |Inorder(Node(y, left0, right0))|, 0
    {
        LemmaBinarySearchSubtree(y, left0, right0);

        if (x > y)
        {
            var right := InsertBST(right0, x);

            RootGreaterThanLeftSubtree(y, left0, right0);
            RootLesserThanRightSubtree(y, left0, right0);
            
            LemmaJoinTrees(y, left0, right);
            
            t := Node(y, left0, right);
        }
        else
        {
            var left := InsertBST(left0, x);

            RootGreaterThanLeftSubtree(y, left0, right0);
            RootLesserThanRightSubtree(y, left0, right0);

            LemmaJoinTrees(y, left, right0);

            assert(Ascending(Inorder(left) + [y] + Inorder(right0)));
            assert(BST(Node(y, left, right0)));

            t := Node(y, left, right0);
        }
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
