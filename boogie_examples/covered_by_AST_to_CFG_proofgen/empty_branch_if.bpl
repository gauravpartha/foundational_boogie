procedure empty_branch_if() {
    var x : int;

    havoc x;
    if(x > 5)
    {

    }
    else
    {
        x := 6;
    }
    assert x > 5;
}