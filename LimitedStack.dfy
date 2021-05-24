
class {:autocontracts} LimitedStack
{
    //Abstração
    ghost const g_MaxSize: nat;
    ghost var g_Stack: seq<nat>;

    //Implementação
    var stackArray: array<nat>;
    const max: nat;
    var tail: nat;

    //Invariante de classe
    predicate Valid() reads this
    {
        max > 0
        && stackArray.Length == max
        && 0 <= tail <= max
        && g_MaxSize == max
        && g_Stack == stackArray[0..tail]
    }

    constructor (m:nat) requires m > 0 ensures g_MaxSize == m ensures g_Stack == []
    {
        max := m;
        stackArray := new nat[m];
        tail := 0;
        g_MaxSize := max;
        g_Stack := [];
    }

    method add(e:nat) returns (b:bool) 
    ensures b != (old(|g_Stack|) >= g_MaxSize)
    ensures ((b == false && (g_Stack == old(g_Stack))) || (b == true && (g_Stack == (old(g_Stack) + [e]))))
    {
        if tail >= max{
           b := false;
        }else {
            stackArray[tail] := e;
            tail := tail + 1;
            g_Stack := g_Stack + [e];
            b := true;
        }
    }


    method remove() returns (e:nat)
    requires |g_Stack| > 0
    ensures e == old(g_Stack)[|old(g_Stack)|-1]
    ensures g_Stack == old(g_Stack)[..|old(g_Stack)|-1]
    {
        e := stackArray[tail-1];
        tail := tail - 1;
        g_Stack := g_Stack[..|g_Stack|-1];
    }


    // method reverse()
    // requires |g_Stack| > 0
    // ensures forall k | 0 == k < |g_Stack| :: g_Stack[k] == old(g_Stack)[|old(g_Stack)|-1-k]
    // {
    //     var aux := new nat[max];
    //     forall k | 0 == k < stackArray.Length 
    //     {
    //         aux[k] := stackArray[stackArray.Length-1-k];
    //     }
    //     a := aux;
    //     g_Stack := stackArray[0..];
    // }


    method get() returns (e:nat)
    requires  0 < |g_Stack| <= g_MaxSize
    ensures e == g_Stack[|g_Stack|-1]
    ensures g_Stack == old(g_Stack)
    {
        e := stackArray[tail-1];
    }
    

    method isFull() returns (b:bool)
    ensures ((b == false && (|g_Stack| < g_MaxSize)) || (b == true && (|g_Stack| == g_MaxSize)))
    ensures g_Stack == old(g_Stack)
    {
        b := !!(max <= tail);
    }

    method isEmpty() returns (b:bool)
    ensures ((b == false && (|g_Stack| > 0)) || (b == true && (|g_Stack| == 0)))
    ensures g_Stack == old(g_Stack)
    {
        b := !!(tail == 0);
    }

    method count() returns (n:nat)
    ensures n == |g_Stack|
    ensures g_Stack == old(g_Stack)
    {
        return tail;
    }

    method maxSize() returns (n:nat)
    ensures n == g_MaxSize
    ensures g_Stack == old(g_Stack)
    {
        return max;
    }
}

method Main()
{
    // tests
    var max := 2;
    var stack := new LimitedStack(max);

    var size := stack.maxSize();
    assert size == 2;

    var empty := stack.isEmpty();
    assert empty == true;

    var result := stack.add(1);
    assert result == true;

    var count := stack.count();
    assert count == 1;
  
    var get1 := stack.get();
    assert get1 == 1;

    var full := stack.isFull();
    assert full == false;

    var empty2 := stack.isEmpty();
    assert empty2 == false;

    var result2 := stack.add(2);
    assert result2 == true;

    var count2 := stack.count();
    assert count2 == 2;

    var full2 := stack.isFull();
    assert full2 == true;

    var poped := stack.remove();
    assert poped == 2;

    var get2 := stack.get();
    assert get2 == 1;

    var size2 := stack.maxSize();
    assert size2 == 2;

    /////////////////////////////////////////

    var testStack := new LimitedStack(2);

    var t1 := testStack.add(1);
    var cc  := testStack.add(2);
    //testStack.reverse();
    var get := testStack.get();

    assert get == 2;
}