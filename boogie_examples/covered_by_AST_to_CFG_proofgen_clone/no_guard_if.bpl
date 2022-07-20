procedure no_guard_if() {
    var x : int;

    havoc x;
    if(*)
    {
        x := 0;
    }
    else
    {
        x := 1;
    }
    
}