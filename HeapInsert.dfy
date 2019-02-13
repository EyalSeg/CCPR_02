include "CCPR191-HeapSort-complete-30Dec18.dfy"

predicate HeapExceptK(a : seq<int>, heapsize : nat, k : nat)
    requires heapsize <= |a|
{
    ph(a, IndexSet(0, heapsize) - {k})
}

predicate Inv(a : seq<int>, heapsize : nat, i : nat, setToBe : multiset<int>)
    //requires heapsize <= |a|
{
    heapsize <= |a| &&
    HeapExceptK(a, heapsize, i) &&
    0 <= i < heapsize <= |a| &&
    multiset(a[..heapsize]) == setToBe &&
    forall j :: 0 <= j < heapsize && AncestorIndex(i, j) ==> a[i] >= a[j]
}

method HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{
    // assingment
    AddXToLeaf(a, heapsize, x);
    a[heapsize] := x;

    // introduce logical constant
    ghost var setToBe := multiset(old(a[..heapsize])+[x]);
    
    SiftLastItem(a, heapsize + 1, setToBe);
}

method SiftLastItem(a : array<int>, heapsize:nat,  ghost setToBe : multiset<int>)
    requires 0 < heapsize <= a.Length
	requires hp(a[..], heapsize - 1)
    requires multiset(a[..heapsize]) == setToBe

    ensures hp(a[..], heapsize)
    ensures multiset(a[..heapsize]) == setToBe
	modifies a
    {
        WeakenPrecondForIteration(a, heapsize, setToBe);
        var i:= SiftLastItem_Iterate(a, heapsize, heapsize - 1, setToBe);
        StrengthenPostFromIteration(a, heapsize, setToBe, i);
    }

lemma AddXToLeaf(a : array<int>, heapsize:nat, itemToAdd : int)
    requires heapsize < a.Length
	requires hp(a[..], heapsize)
    ensures multiset(a[..heapsize+1][heapsize := itemToAdd][..heapsize + 1]) ==
            multiset(old(a[..heapsize])+[itemToAdd])
    {
        ghost var a' := a[..heapsize + 1][heapsize := itemToAdd];
        assert a'[..heapsize] == a[..heapsize];
        assert a'[..heapsize + 1] == a[..heapsize] + [a'[heapsize]];

        assert multiset(a[..heapsize+1][heapsize := itemToAdd][..heapsize]) == multiset(a[..heapsize]);
    }

lemma WeakenPrecondForIteration(a : array<int>, heapsize:nat, setToBe : multiset<int>)
    requires 0 < heapsize <= a.Length
	requires hp(a[..], heapsize - 1)
    requires multiset(a[..heapsize]) == setToBe

    ensures  heapsize <= a.Length
    ensures Inv(a[..], heapsize, heapsize - 1, setToBe)
    {
    }

lemma StrengthenPostFromIteration(a : array<int>, heapsize:nat, setToBe : multiset<int>, i : nat)
    requires Inv(a[..], heapsize, i, setToBe)
    requires ! (i > 0)
    ensures hp(a[..], heapsize)
    ensures multiset(a[..heapsize]) == setToBe
    {}

method SiftLastItem_Iterate(a : array<int>, heapsize:nat, i0 : nat, ghost setToBe : multiset<int>) returns (i : nat)
    requires Inv(a[..], heapsize, i0, setToBe)

    ensures Inv(a[..], heapsize, i, setToBe)
    ensures i == 0

    modifies a
{
    i := i0;

     while i > 0
        invariant Inv(a[..], heapsize, i, setToBe)
        decreases i
    {
        i := LoopBody(a, heapsize, i, setToBe);
    }
}

method {:verify true} LoopBody (a : array<int>, heapsize:nat, i0 : nat, ghost setToBe : multiset<int>) returns (i : nat)
    requires i0 > 0
    requires Inv(a[..], heapsize, i0, setToBe)

    ensures i < i0
    ensures Inv(a[..], heapsize, i, setToBe)

    modifies a
{
    var ancestor := (i0 - 1) / 2;

    if (a[i0] > a[ancestor])
    {
        i := Swap(a, heapsize, i0, setToBe);
    }
    else
    {
        i := Skip(a, heapsize, i0, setToBe);
    }
}

method Swap (a : array<int>, heapsize:nat, i0 : nat, ghost setToBe : multiset<int>) returns (i : nat)
    requires i0 > 0
    requires Inv(a[..], heapsize, i0, setToBe)
    requires a[i0] > a[(i0 - 1) / 2]

    ensures Inv(a[..], heapsize, i, setToBe)
    ensures i < i0

    modifies a
    {
        LemmaSwap(a[..], heapsize, i0, setToBe);
        a[i0], a[((i0 - 1) / 2)], i := a[(i0 - 1) / 2], a[i0], ((i0 - 1) / 2);
    } 

method Skip(a : array<int>, heapsize:nat, i0 : nat, ghost setToBe : multiset<int>) returns (i : nat)
requires i0 > 0
    requires Inv(a[..], heapsize, i0, setToBe)
    requires a[i0] <= a[(i0 - 1) / 2]

    ensures Inv(a[..], heapsize, i, setToBe)
    ensures i < i0

    modifies a
{
    LemmaSkip(a[..], heapsize, i0, setToBe);
    i := (i0 - 1) / 2;
}

lemma LemmaSkip(a : seq<int>, heapsize:nat, i : nat, setToBe : multiset<int>)
    requires i > 0
    requires Inv(a, heapsize, i, setToBe)
    requires a[i] <= a[(i-1) / 2]

    ensures Inv(a, heapsize, (i-1)/2, setToBe)
    {
        ghost var ancestor := (i - 1)/2;
        assert AncestorIndex(ancestor, i);

        assert forall j :: 
            i <= j < heapsize &&
            AncestorIndex(i, j) ==>
            a[i] >= a[j];

        DirectAncestorLemma(ancestor, i);        

        assert forall j ::
            0 <= j < i &&
            AncestorIndex(j, i) ==>
                AncestorIndex(j, ancestor);
    }

lemma LemmaSwap(a : seq<int>, heapsize:nat, i : nat, setToBe : multiset<int>)
    requires i > 0
    requires Inv(a, heapsize, i, setToBe)
    requires a[i] > a[(i-1) / 2]

    ensures Inv(a[ i := a[(i-1)/2]][(i-1)/2 := a[i]], heapsize, (i - 1) / 2, setToBe)
    {
        ghost var ancestor := (i - 1)/2;
        assert AncestorIndex(ancestor, i);

        ghost var change1 := a[ i := a[ancestor]];
        ghost var change2 := change1[ancestor := a[i]];

        assert forall j ::
            0 <= j < heapsize && 
            j != i && j != ancestor ==>
                change2[j] == a[j];

        assert forall j, k ::
            0 <= j <heapsize &&
            0 <= k <heapsize &&
            j != i && j != ancestor &&
            k != i && k != ancestor &&
            AncestorIndex(j, k) ==>
                change2[j] >= change2[k];

        assert forall j ::
            0 <= j < heapsize && 
            j != ancestor &&
            AncestorIndex(i, j) ==>
                change2[i] >= change2[j];

        DirectAncestorLemma(ancestor, i);
        
        assert forall j ::
            0 <= j < i && 
            j != ancestor &&
            AncestorIndex(j, i) ==>
                change2[j] >= change2[i];
    

        assert forall j, k ::
            0 <= j < heapsize && j != ancestor &&
            0 <= k < heapsize && k != ancestor &&
            AncestorIndex(j, k) ==>
                change2[j] >= change2[k];

    }


predicate DirectAncestor(ancestor : nat, i : nat)
{
    (i - 1) / 2 == ancestor
}

lemma DirectAncestorLemma(ancestor:nat, i : nat)
    requires DirectAncestor(ancestor, i)
    ensures forall j :: ancestor < j < i ==> !AncestorIndex(j, i)  
    ensures forall j :: 0 <= j < i && j != ancestor ==> (AncestorIndex(j, i) ==> AncestorIndex(j, ancestor))



method GetAncestorIndex(i : nat) returns (j : nat)
    requires i >= 1
    ensures j < i
    ensures AncestorIndex(j, i)
{
    j := ((i - 1) as real / 2 as real).Floor as nat;
}
