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
		if Guard1(a)
		{
			b := Updateb1(a,b);
		}
		else
		{
			b := Updateb2(a,b);
		}
	}
predicate method Guard1(a: array<int>)
{
	a.Length <= 1
}
method Updateb1(a: array<int>,b0: array<int>) returns (b: array<int>)
	requires Guard1(a)
    ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{   b:=b0;
    // assignment
	LemmaUpdateb1(a,b);
	b := a;
}
lemma LemmaUpdateb1 (a:array<int>,b: array<int>)
	requires Guard1(a)
    ensures a.Length == a.Length && Sorted(a) && multiset(a[..]) == multiset(a[..])
{}
method Updateb2(a: array<int>,b0: array<int>) returns (b: array<int>)
    decreases a.Length,1
	requires !Guard1(a)
    ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{   b:=b0;
    // assignment
	// LemmaUpdateb2(a,b); // TODO Lemma
	b := Merge_NotEmptyOrSingle(a,b);
}
// lemma LemmaUpdateb2 (a:array<int>,b: array<int>)
// 	requires !Guard1(a)
//     ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
// {}

//----------------------------------------------------------------------------------------
method Merge_NotEmptyOrSingle(a: array<int>,b0: array<int>) returns (b: array<int>)
// todo: refine
	requires !Guard1(a)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length, 0
{   
	// introduce local variable
	var  mid:nat, left:seq<int>, right:seq<int>,leftArr: array<int>,rightArr: array<int>;
    leftArr,rightArr,mid:=init(a,b0,leftArr,rightArr,mid);
	b:=merging (a,b0,leftArr,rightArr) ;
}

lemma LemmaUpdatebmid(a: array<int>,mid0:nat) 
	requires !Guard1(a) 
    ensures  a.Length / 2 == a.Length / 2;	
{}
method   UpdatebMid (a: array<int>,mid0:nat) returns (mid:nat)
	 requires !Guard1(a)
     ensures  mid == a.Length / 2;	
{  	
mid:=mid0;
mid:=a.Length / 2;
}
lemma LemmaUpdateLeftarrRightarr(a: array<int>,b0: array<int>,leftArr: array<int>,rightArr: array<int>,mid:nat) 
	requires !Guard1(a) && mid==a.Length/2
    ensures mid < a.Length && a.Length-mid < a.Length && a[..]==a[..mid]+a[mid..]
{}
//---------------
method  UpdatebLeftArrRightArr(a: array<int>,b0: array<int>,leftArr0: array<int>,rightArr0: array<int>,mid:nat) returns (leftArr: array<int>,rightArr: array<int>)
	requires !Guard1(a)&& mid==a.Length/2
    ensures leftArr.Length < a.Length && rightArr.Length < a.Length && 
	 leftArr[..]+rightArr[..]==a[..]
{  	
	// var left:seq<int>, right:seq<int>,mid:nat;
    // LemmaUpdatebleftRight(a,b0,right,left,mid);
	//  left, right := UpdatebMidLeftRight(a,b0,right,left);
	 leftArr :=UpdatebLeftArr(a,b0,leftArr,mid);
	 rightArr := UpdatebRightArr(a,b0,rightArr,mid);

}
lemma LemmaUpdatebleftRight(a: array<int>,b0: array<int>,left:  seq<int>,right:  seq<int>,mid:nat) 
	requires !Guard1(a) && mid == a.Length / 2;	
    ensures a[..] ==  a[.. mid] +  a[mid..]
{}


method  UpdatebLeftArr (a: array<int>,b0: array<int>,leftArr0: array<int>,mid:nat) returns (left:array<int>)
	requires !Guard1(a) && mid == a.Length / 2;	
     ensures left[..] == a[.. mid]
{  	
left:=leftArr0;
LemmaUpdateleftArr(a,b0,leftArr0,mid);
 left:=SeqToArray(a[.. mid]);
}
lemma LemmaUpdateleftArr(a: array<int>,b0: array<int>,leftArr:array<int>,mid:nat) 
	requires !Guard1(a) && mid == a.Length / 2;	
     ensures a[.. mid] == a[.. mid]
{}

method  UpdatebRightArr (a: array<int>,b0: array<int>,rightArr0: array<int>,mid:nat) returns (rightArr:array<int>)
	requires !Guard1(a) && mid == a.Length / 2;	
     ensures rightArr[..] == a[ mid..]
{  	
rightArr:=rightArr0;
LemmaUpdaterightArr(a,b0,rightArr0,mid);
 rightArr:=SeqToArray(a[ mid..]);
}
lemma LemmaUpdaterightArr(a: array<int>,b0: array<int>,rightArr:array<int>,mid:nat) 
	requires !Guard1(a) && mid == a.Length / 2;	
     ensures a[ mid..] == a[ mid..]
{}

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


//-------------------------------------------------
method  init (a:array<int>,b0: array<int>,leftArr0: array<int>,rightArr0: array<int>,mid0:nat) returns (leftArr: array<int>,rightArr: array<int>,mid:nat)
	requires !Guard1(a) 
	ensures  leftArr.Length < a.Length && rightArr.Length < a.Length && 
	 leftArr[..]+rightArr[..]==a[..]

{  mid,leftArr,rightArr:=mid0,leftArr0,rightArr0;
	LemmaUpdatebmid(a,mid);
    mid:=UpdatebMid(a,mid);
    LemmaUpdateLeftarrRightarr(a,b0,leftArr,rightArr,mid);
	 leftArr,rightArr :=UpdatebLeftArrRightArr(a,b0,leftArr,rightArr,mid);
}
//TODO:continue
method  merging (a:array<int>,b0: array<int>,leftArr0: array<int>,rightArr0: array<int>) returns (b: array<int>)
	requires !Guard1(a) &&  leftArr0.Length < a.Length && rightArr0.Length < a.Length && 
	 leftArr0[..]+rightArr0[..]==a[..]
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length, 0
{  	var leftArr:array<int>,rightArr:array<int>;
    leftArr:=leftArr0;
	leftArr := MergeSort(leftArr0);
	rightArr:=rightArr0;
	rightArr := MergeSort(rightArr0);

	b := new int[a.Length];
	Merge(b, leftArr, rightArr);
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
	{
		// Weaken precondition
		IteratePreconditionLemma(b, c, d);
		Iterate(b, c, d, 0, 0);
	}

lemma IteratePreconditionLemma(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures MergeIterationInvariant(b, c, d, 0, 0) 
{
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
	
	&& SortedSequence(b[..i+j])
//	&& (forall x :: x == i+j ==> SortedSequence(b[..x]))

	&& multiset(b[..i+j]) == multiset(c[..i])+multiset(d[..j])
}

method {:verify true} Iterate(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	modifies b
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])

	{
		var i: nat, j: nat := i0, j0;

		while i+j < b.Length
			invariant MergeIterationInvariant(b, c, d, i, j);
			decreases b.Length - (i+j)
			{
				i, j := MergeIterateStep(b, c, d, i, j);
			}

		// Strengthen postcondition
		IteratePostcondition(b, c, d, i, j);
			
	}

lemma IteratePostcondition(b: array<int>, c: array<int>, d: array<int>, i : nat, j:nat)
	requires MergeIterationInvariant(b, c, d, i, j)
	requires i + j >= b.Length
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	{
		assert(multiset(b[..i+j]) == multiset(c[..i])+multiset(d[..j]));
		assert(i + j == b.Length);
		assert(i == c.Length);
		assert(j == d.Length);

		assert(c[..] == c[..i]);
		assert(d[..] == d[..j]);
		assert(b[..] == b[.. i + j]);
		
	}

method MergeIterateStep(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat) returns (i:nat, j:nat)
	requires b.Length > i0 + j0
	requires MergeIterationInvariant(b, c, d, i0, j0)
	ensures MergeIterationInvariant(b, c, d, i, j)
	ensures i + j > i0 + j0
	
	modifies b

{
	// Weaken precondition
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
	ensures i + j > i0 + j0

	modifies b
	{
		// Leading assignment
		b[i0 + j0] := c[i0];

		TakeFromCLemma(b, c, d, i0, j0);
		i, j := i0 + 1, j0;
	}

method TakeFromD(b: array<int>, c: array<int>, d: array<int>, i0 : nat, j0:nat) returns (i:nat, j:nat)
	requires MergeIterationInvariant(b, c, d, i0, j0)
	requires j0 < d.Length
	requires i0 == c.Length || c[i0] >= d[j0]
	ensures MergeIterationInvariant(b, c, d, i, j)
	ensures i + j > i0 + j0

	modifies b
	{	
		// Leading assignment
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


