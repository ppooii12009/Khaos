module JSTRINGBUILDER-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports AUXILIARY-SYNTAX
    imports MLIST-SYNTAX

syntax Id ::= "StringBuilder"       [token]

endmodule

module JSTRINGBUILDER
    imports JSTRINGBUILDER-SYNTAX
    imports DOMAINS
    imports CONFIGURATION

rule    <k> addBuildinClass(1) => addBuildinClass(2) ... </k>
        <classes>
        ...
        (.Bag =>
            <classData>
                <className> StringBuilder </className>
                <baseClass> Object </baseClass>
                <declarations> 
                    string String2Id("str"), .Vals; 
                    void StringBuilder(.Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = "";
                    }
                    void StringBuilder(string String2Id("s"), .Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = String2Id("s");
                    }
                    string String2Id("toString")(.Parameters) : _RESULT_ .Specifications
                    {
                        return this.String2Id("str");
                    }
                    int String2Id("length")(.Parameters) : _RESULT_ .Specifications
                    {
                        return this.String2Id("str").size();
                    }
                    StringBuilder String2Id("append")(string String2Id("s"), .Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = this.String2Id("str") + String2Id("s");
                        return this;
                    }
                    StringBuilder String2Id("append")(int String2Id("i"), .Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = this.String2Id("str") + String2Id("i");
                        return this;
                    }
                    StringBuilder String2Id("append")(bool String2Id("b"), .Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = this.String2Id("str") + String2Id("b");
                        return this;
                    }
                    StringBuilder String2Id("append")(StringBuilder String2Id("sb"), .Parameters) : _RESULT_ .Specifications
                    {
                        this.String2Id("str") = this.String2Id("str") + String2Id("sb").String2Id("str");
                        return this;
                    }
                    StringBuilder String2Id("append")(#AbstractListType String2Id("l"), .Parameters) : _RESULT_ .Specifications
                    {
                        int String2Id("s") = String2Id("l").size();
                        this.String2Id("str") = this.String2Id("str") + "[";
                        for(int String2Id("i") = 0; String2Id("i") < String2Id("s") ; String2Id("i")++)
                        {
                            this.String2Id("str") = this.String2Id("str") + (String2Id("l").get(String2Id("i"))).String2Id("toString")(.Vals);
                            if(String2Id("i") < String2Id("s") - 1)
                            {
                                this.String2Id("str") = this.String2Id("str") + ", ";
                            }
                        }
                        this.String2Id("str") = this.String2Id("str") + "]";
                        return this;
                    }
                </declarations>
            </classData>
        )
        </classes>
        <inheritanceMap> 
            IMap:Map => IMap[String2Id("StringBuilder") <- Object]
        </inheritanceMap>

endmodule