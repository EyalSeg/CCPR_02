predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length, 1
	{
		if a.Length <= 1
		{
			b := a;
		}
		else
		{
			b := Merge_NotEmptyOrSingle(a);
		}
	}

method Merge_NotEmptyOrSingle(a: array<int>) returns (b: array<int>)
// todo: refine
	requires a.Length > 1
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length, 0
{
	var mid := a.Length / 2;
	var left, right := a[.. mid], a[mid..];

	assert(a[..] == left[..] + right[..]);

	var leftArr := SeqToArray(left);
	var rightArr := SeqToArray(right);

	assert(leftArr.Length < a.Length && rightArr.Length < a.Length);
	
	leftArr := MergeSort(leftArr);
	rightArr := MergeSort(rightArr);

	b := new int[a.Length];
	Merge(b, leftArr, rightArr);
}

method SeqToArray(a: seq<int>) returns (b: array<int>)
ensures a == b[..]
{
	b := new int[|a|];
	var i := 0;

	while i < |a|
	decreases |a| - i
	invariant |a| >= i
	invariant a[..i] == b[..i]
	{
		b[i] := a[i];
		i := i + 1;
	}
}


method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
	{
		assert(MergeIterationInvariant(b, c, d, 0, 0));
		Iterate(b, c, d, 0, 0);
	}

predicate MergeIterationInvariant(b: array<int>, c: array<int>, d: array<int>, i : nat, j:nat)
	reads(b)
	reads(c)
	reads(d)
{	
	b != c && b != d && b.Length == c.Length + d.Length
	&& 0 <= i <= c.Length
	&& 0 <= j <= d.Length 
	&& i + j <= b.Length
	&& Sorted(c)
	&& Sorted(d)

	// the current item at c, d is greater than every item in b
	&& (i < c.Length ==> forall x :: 0 <= x < i + j ==> b[x] <= c[i])
	&& (j < d.Length ==> forall x :: 0 <= x < i + j ==> b[x] <= d[j])
	
	// SortedSequence(b[..i+j]) could not be safely inlined
	&& (forall x :: x == i+j ==> SortedSequence(b[..x]))

	&& multiset(b[..i+j]) == multiset(c[..i])+multiset(d[..j])
}

method {:verify false} Iterate(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	modifies b
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])

	{
		var i, j := i0, j0;

		while i+j < b.Length
			invariant MergeIterationInvariant(b, c, d, i, j);
			decreases b.Length - (i+j)
			{
				i, j := MergeIterateStep(b, c, d, i, j);
			}

	// lemma that proves that inv + !guard => post		
	}


method MergeIterateStep(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat) returns (i:nat, j:nat)
	requires b.Length > i0 + j0
	requires MergeIterationInvariant(b, c, d, i0, j0)
	ensures MergeIterationInvariant(b, c, d, i, j)
	
	modifies b

{
	// todo: seperate to a weaken precondition function?
	MergeLoopLemma(b, c, d, i0, j0);

	if i0 == c.Length
	{
		// Weaken precondition to match TakeFrom's pre
		i, j := TakeFromD(b, c, d, i0, j0);
	}
	else if j0 == d.Length
	{
		// Weaken precondition to match TakeFrom's pre
		i, j := TakeFromC(b, c, d, i0, j0);
	}
	else if c[i0] > d[j0]
	{
		// Weaken precondition to match TakeFrom's pre
		i, j := TakeFromD(b, c, d, i0, j0);
	}
	else
	{
		// Weaken precondition to match TakeFrom's pre
		i, j := TakeFromC(b, c, d, i0, j0);
	}
}



method TakeFromC(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat) returns (i:nat, j:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	requires i0 < c.Length
	requires j0 == d.Length || d[j0] >= c[i0]
	ensures MergeIterationInvariant(b, c, d, i, j)

	modifies b
	{
		assert(MergeIterationInvariant(b, c, d, i0, j0));

		// TODO: prove
		b[i0 + j0] := c[i0];

		assert(MergeIterationInvariant(b, c, d, i0, j0));

		TakeFromCLemma(b, c, d, i0, j0);
		i, j := i0 + 1, j0;
	}

method TakeFromD(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat) returns (i:nat, j:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	requires j0 < d.Length
	requires i0 == c.Length || c[i0] >= d[j0]
	ensures MergeIterationInvariant(b, c, d, i, j)

	modifies b
	{	
		assert(MergeIterationInvariant(b, c, d, i0, j0));
		ghost var k := i0+j0;

		// TODO: prove
		b[i0 + j0] := d[j0];
		
		TakeFromDLemma(b, c, d, i0, j0);
		i, j := i0, j0 + 1;
	}	

lemma TakeFromCLemma(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	requires i0 < c.Length
	requires j0 == d.Length || d[j0] >= c[i0]
	requires b[i0 + j0] == c[i0]
	ensures MergeIterationInvariant(b, c, d, i0+1, j0)
	{
		ghost var i, j := i0 + 1, j0;
		ghost var k := i + j;

		assert(SortedSequence(b[..k]));
	}

lemma TakeFromDLemma(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	requires j0 < d.Length
	requires i0 == c.Length || c[i0] >= d[j0]
	requires b[i0 + j0] == d[j0]
	ensures MergeIterationInvariant(b, c, d, i0, j0+1)
	{

		ghost var i, j := i0, j0 + 1;
		ghost var k := i + j;
		assert(SortedSequence(b[..k]));
	}



lemma MergeLoopLemma(b: array<int>, c: array<int>, d: array<int>, i : nat, j:nat)
requires MergeIterationInvariant(b, c, d, i, j)
requires i+j < b.Length
ensures i == c.Length ==> j < d.Length
ensures j == d.Length ==> i < c.Length
{
}

method Main() {
	var a := new int[3];
	a[0], a[1], a[2] := 4, 8, 6;
	var q0 := a[..];
	assert q0 == [4,8,6];
	a := MergeSort(a);
	assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4,6,8];
}


