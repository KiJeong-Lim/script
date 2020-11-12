# scripts

# Aladdin

## syntax

```
Term ::=
    | LVar LogicVar
    | DCon Constant
    | IApp Term Term
    | IAbs (Term -> Term)
    ;

Atom ::=
    | LVar LogicVar
    | DCon Constant
    | IApp Atom Term
    ;

AtomR ::=
    | DCon Constant
    | IApp AtomR Term
    ;

Goal ::=
    | GTrue
    | GFail
    | GCut
    | GAnd Goal Goal
    | GOr Goal Goal
    | GImply Fact Goal
    | GSigma (Term -> Goal)
    | GPi (Term -> Goal)
    | GEqn Term Term
    | GAtom Atom
    | GAssert AtomR
    ;

Fact ::=
    | FAtom AtomR
    | FPi (Term -> Fact)
    | FIf Fact Goal
    ;

coerce : Atom -> Term;
coerce (LVar var) := LVar var;
coerce (DCon con) := DCon con;
coerce (IApp atom_1 term_2) := IApp (coerce atom_1) term_2;

coerce : AtomR -> Term;
coerce (DCon con) := DCon con;
coerce (IApp rigid_atom_1 term_2) := IApp (coerce rigid_atom_1) term_2;

coerce : Goal -> Term;
coerce (GTrue) := DCon "__g_true";
coerce (GFail) := DCon "__g_fail";
coerce (GCut) := DCon "__g_cut";
coerce (GAnd goal_1 goal_2) = IApp (IApp (DCon "__g_and" (coerce goal_1)) (coerce goal_2));
coerce (GOr goal_1 goal_2) = IApp (IApp (DCon "__g_or" (coerce goal1_)) (coerce goal_2));
coerce (GImply fact_1 goal_2) = IApp (IApp (DCon "__g_imply" (coerce fact_1)) (coerce goal_2));
coerce (GSigma goal_1) = IApp (DCon "__g_sigma") (IAbs (coerce . goal_1));
coerce (GPi goal_1) = IApp (DCon "__g_pi") (IAbs (coerce . goal_1));
coerce (GEqn term_1 term_2) = IApp (IApp (DCon "__g_eqn") (coerce term_1)) (coerce term_2);
coerce (GAtom atom) := coerce atom;

coerce : Fact -> Term;
coerce (FAtom rigid_atom) := coerce rigid_atom;
coerce (FPi fact_1) := IApp (DCon "__f_pi") (IAbs (coerce . fact_1));
coerce (FIf fact_1 goal_2) := IApp (IApp (DCon "__f_if") (coerce fact_1)) (coerce goal_2);
```

## semantics

```
env |- ([(Context mempty theEmptyLabeling [], [Cell program 0 query])], []) ~> ((Context theta _ []), []) : _, _)
----------------------------------------------------------------------------------------------------------------- Main
env |- program ?- query ~~> putStrLn ("Yes, the answer substitution is:" ++ show theta)

---------------------------------------------- Supply
env |- ([], stack : stacks) ~> (stack, stacks)

env |- ((ctx, cells) : stack, stacks) ~> (stack', stacks')
----------------------------------------------------------------------------------- True
env |- ((ctx, Cell facts level GTrue : cells) : stack, stacks) ~> (stack', stacks')

env |- (stack, stacks) ~> (stack', stacks')
----------------------------------------------------------------------------------- Fail
env |- ((ctx, Cell facts level GFail : cells) : stack, stacks) ~> (stack', stacks')

env |- ([(ctx, cells)], []) ~> (stack', stacks')
---------------------------------------------------------------------------------- Cut
env |- ((ctx, Cell facts level Gcut : cells) : stack, stacks) ~> (stack', stacks')

env |- ((ctx, Cell facts level goal_1 : Cell facts level goal_2 : cells) : stack, stacks) ~> (stack', stacks')
-------------------------------------------------------------------------------------------------------------- And
env |- ((ctx, Cell facts level (GAnd goal_1 goal_2) : cells) : stack, stacks) ~> (stack', stacks')

env |- ((ctx, Cell facts level goal_1 : cells) : (ctx, Cell facts level goal_2 : cells) : stack, stacks) ~> (stack', stacks')
----------------------------------------------------------------------------------------------------------------------------- Or
env |- ((ctx, Cell facts level (GOr goal_1 goal_2) : cells) : stack, stacks) ~> (stack', stacks')

env |- ((ctx, Cell (fact_1 : facts) level goal_2 : cells) : stack, stacks) ~> (stack', stacks')
---------------------------------------------------------------------------------------------------- Imply
env |- ((ctx, Cell facts level (GImply fact_1 goal_2) : cells) : stack, stacks) ~> (stack', stacks')

env ~~[ uni <- getNewUnique ]~> env'
lens (labeling ~~[ enrollLVar (LVar uni) level ]~> labeling') : ctx +-> ctx'
env' |- ((ctx', Cell facts level (goal_1 (LVar uni) : cells)) : stack, stacks) ~> (stack', stacks')
--------------------------------------------------------------------------------------------------- Sigma
env |- ((ctx, Cell facts level (GSigma goal_1) : cells) : stack, stacks) ~> (stack', stacks')

env ~~[ uni <- getNewUnique ]~> env'
lens (labeling ~~[ enrollLVar (NCon uni) (level + 1) ]~> labeling') : ctx +-> ctx'
env' |- ((ctx', Cell facts (level + 1) (goal_1 (NCon uni)) : cells) : stack, stacks) ~> (stack', stacks')
--------------------------------------------------------------------------------------------------------- Pi
env |- ((ctx, Cell facts level (GPi goal_1) : cells) : stack, stacks) ~> (stack', stacks')

new_stack :=
    [ (Context (new_theta <> theta) new_labeling new_constraints, applyVarBinding new_theta (Cell facts level goal : cells))
    | FAtom fact <- facts
    , (labeling, env) ~~[ (foldl NApp (NCon p') args', goal) <- instantiateFact fact ]~> (labeling', env')
    , p == p'
    , length args == length args'
    , env' |- ([ Disagreement (lhs :=?=: rhs) | (lhs, rhs) <- zip args args' ]) ++ constraints ~~[ solve facts labeling' ]~> solutions
    , (Solution new_theta new_labeling, new_constraints) <- solutions
    ]
------------------------------------------------------------------------------------------------------------------------------------------------------- Atom
env |- ((Context theta labeling constraints, Cell facts level (GAtom (foldl NApp (NCon p) args) : cells)) : stack, stacks) ~> (new_stack, stack : stacks)

new_stack :=
    [ (Context (new_theta <> theta) new_labeling new_constraints, applyVarBinding new_theta (Cell facts level goal : cells))
    | env' |- Disagreement (lhs :=?=: rhs) : constraints ~~[ solve facts labeling' ]~> solutions
    , (Solution new_theta new_labeling, new_constraints) <- solutions
    ]
------------------------------------------------------------------------------------------------------------------------------------ Eqn
env |- ((Context theta labeling constraints, Cell facts level (GEqn lhs rhs : cells)) : stack, stacks) ~> (new_stack ++ stack, stacks)

env |- ((Context theta labeling (constraint : constraints), cells) : stack, stacks) ~> (stack', stacks')
--------------------------------------------------------------------------------------------------------------------------------- Assert 
env |- ((Context theta labeling constraints, Cell facts level (GAssert constraint) : cells) : stack, stacks) ~> (stack', stacks')
```

# Jasmine

# Abu

# license

```
    MIT License

    Copyright (c) 2020 임기정

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE.
```

``base``:

```
    This library (libraries/base) is derived from code from several
    sources: 

    * Code from the GHC project which is largely (c) The University of
        Glasgow, and distributable under a BSD-style license (see below),

    * Code from the Haskell 98 Report which is (c) Simon Peyton Jones
        and freely redistributable (but see the full license for
        restrictions).

    * Code from the Haskell Foreign Function Interface specification,
        which is (c) Manuel M. T. Chakravarty and freely redistributable
        (but see the full license for restrictions).

    The full text of these licenses is reproduced below.  All of the
    licenses are BSD-style or compatible.

    -----------------------------------------------------------------------------

    The Glasgow Haskell Compiler License

    Copyright 2004, The University Court of the University of Glasgow. 
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice,
    this list of conditions and the following disclaimer.
    
    - Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.
    
    - Neither name of the University nor the names of its contributors may be
    used to endorse or promote products derived from this software without
    specific prior written permission. 

    THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY COURT OF THE UNIVERSITY OF
    GLASGOW AND THE CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
    INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    UNIVERSITY COURT OF THE UNIVERSITY OF GLASGOW OR THE CONTRIBUTORS BE LIABLE
    FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
    OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
    DAMAGE.

    -----------------------------------------------------------------------------

    Code derived from the document "Report on the Programming Language
    Haskell 98", is distributed under the following license:

    Copyright (c) 2002 Simon Peyton Jones

    The authors intend this Report to belong to the entire Haskell
    community, and so we grant permission to copy and distribute it for
    any purpose, provided that it is reproduced in its entirety,
    including this Notice.  Modified versions of this Report may also be
    copied and distributed for any purpose, provided that the modified
    version is clearly presented as such, and that it does not claim to
    be a definition of the Haskell 98 Language.

    -----------------------------------------------------------------------------

    Code derived from the document "The Haskell 98 Foreign Function
    Interface, An Addendum to the Haskell 98 Report" is distributed under
    the following license:

    Copyright (c) 2002 Manuel M. T. Chakravarty

    The authors intend this Report to belong to the entire Haskell
    community, and so we grant permission to copy and distribute it for
    any purpose, provided that it is reproduced in its entirety,
    including this Notice.  Modified versions of this Report may also be
    copied and distributed for any purpose, provided that the modified
    version is clearly presented as such, and that it does not claim to
    be a definition of the Haskell 98 Foreign Function Interface.

    -----------------------------------------------------------------------------
```

``containers``:

```
    The Glasgow Haskell Compiler License

    Copyright 2004, The University Court of the University of Glasgow.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice,
    this list of conditions and the following disclaimer.

    - Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

    - Neither name of the University nor the names of its contributors may be
    used to endorse or promote products derived from this software without
    specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY COURT OF THE UNIVERSITY OF
    GLASGOW AND THE CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
    INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    UNIVERSITY COURT OF THE UNIVERSITY OF GLASGOW OR THE CONTRIBUTORS BE LIABLE
    FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
    OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
    DAMAGE.
```

``transformers``:

```
    The Glasgow Haskell Compiler License

    Copyright 2004, The University Court of the University of Glasgow.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice,
    this list of conditions and the following disclaimer.

    - Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

    - Neither name of the University nor the names of its contributors may be
    used to endorse or promote products derived from this software without
    specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY COURT OF THE UNIVERSITY OF
    GLASGOW AND THE CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
    INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    UNIVERSITY COURT OF THE UNIVERSITY OF GLASGOW OR THE CONTRIBUTORS BE LIABLE
    FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
    OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
    DAMAGE.
```

``QuickCheck``:

```
    (The following is the 3-clause BSD license.)

    Copyright (c) 2000-2019, Koen Claessen
    Copyright (c) 2006-2008, Björn Bringert
    Copyright (c) 2009-2019, Nick Smallbone

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice,
    this list of conditions and the following disclaimer.
    - Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
    - Neither the names of the copyright owners nor the names of the
    contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
    A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
    OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
    SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
    LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
    DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
    (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
    OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

``checkers``:

```
    Copyright (c) 2009 Conal Elliott
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
    1. Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
    2. Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
    3. The names of the authors may not be used to endorse or promote products
    derived from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR
    IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
    OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
    IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
    NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
    DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
    (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
    THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

``pretty-terminal``:

```
    Copyright Logan McPhail (c) 2018

    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions are met:

        * Redistributions of source code must retain the above copyright
        notice, this list of conditions and the following disclaimer.

        * Redistributions in binary form must reproduce the above
        copyright notice, this list of conditions and the following
        disclaimer in the documentation and/or other materials provided
        with the distribution.

        * Neither the name of Author name here nor the names of other
        contributors may be used to endorse or promote products derived
        from this software without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
    A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
    OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
    SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
    LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
    DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
    (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
    OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
