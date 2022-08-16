procedure no_guard_empty_branch_if() {
    var x : int;

    havoc x;
    if(*)
    {

    }
    else
    {
        x := 6;
    }
}