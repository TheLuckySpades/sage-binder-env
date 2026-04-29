import time
from sage.combinat.finite_state_machine import FSMState, FSMTransition


#Find the order of all finite special subgroups
def finiteOrder(W):
    orderList=[]
    #if it is finite itself we take that order
    if W.is_finite():
        return W.cardinality()
    M=matrix(W.coxeter_matrix())
    l=M.nrows()
    S=list(range(l))
    for S1 in list(Subsets(S)):
        if len(S1)>0 and len(S1)<l:
            M1=M[list(S1),list(S1)]
            W1=CoxeterGroup(list(M1))
            if W1.is_finite():
                if not (W1.cardinality() in orderList):
                    orderList.append(W1.cardinality())
    order=prod(orderList)
    return order


#I want to see if an element has finite order, m is the largest order of a finite special subgroup
#w is an element of the group, m a strictly positive integer
def elementFinite(w,m):
    #the first check is to avoid the case where mi is \infty, but the implementation uses -1 here
    #don't think the check is actually needed wince reflections are their own inverses and not the unit
    return (w^m).is_one()


#checks is r1 seperates r2 from the identity, a wall seperates itself from the identity is the convention I went with
#either convention requires a case distinction at different parts
#r1, r2 are group elements, m a strictly positive integer
def seperateFromOne(r1,r2,m):
    r=r1*r2
    #check 1: they are inverses
    if (r1*(r2^-1)).is_one():
        return True
    #check 2: they have finite order, i.e. the walls intersect
    if elementFinite(r,m):
        return False
    #check 3: they are distinct and parallel, actual reflection of r2 along r1 if r1*r2*r1^-1, but if that is shorter than r2
    #then r1*r2 has to be shorter as well since as conjugates of simple reflections we can do the simplifications to a geodesi
    #word on both sides, i.e. r1*r2 can be made shorter than r2
    elif (r).length()<(r2).length():
        return True
    else:
        return False


#G is the group, m is it's finite order, since it is used a lot it will be calculated seperately
def wallsOfOne(G,m):
    #fin is the indicator for the process of finding walls, parallel is a statement about the current wall being checked
    fin=False
    parallel=False
    #Initializing the list with the walls of the fundamental chamber, so start check at walls gsg^-1 where g has length 1
    #I might return and change stuff from reduced words to elements, especially since in the FSA I ended up needing elements
    #but reduced words are fantastic for debugging
    n=1
    s=G.simple_reflections()
    H=[]
    for t in s:
        H.append(tuple(t.reduced_word()))
    while fin==False:
        #print statements are debugging artifacts I plan on keeping until I'm done messing with the code
        #print(n)
        #if we find any new walls at our current radius we stop, if we find a new wall we flip this and continue
        fin=True
        #looking at walls at distance n from the identity
        for g in list(G.elements_of_length(n)):
            #got 3 reflections around any point, redcing this to 2 is possible, but I don't know if it would be faster
            for t in s:
                #we assume the new wall is not seperated from 1 until we find a wall in H that does
                parallel=False
                #the reflection we are checking
                gRef=g*t*(g^-1)
                #print(gRef.reduced_word())
                #checking if it is a new one
                for rl in H:
                    #convert the reduced word to group element
                    r=G.from_reduced_word(rl)
                    #check if g is seperated from the unit by this wall, if it is seperated we can ignore it
                    if seperateFromOne(r,gRef,m):
                            parallel=True
                            #print("seperated by ")
                            #print(rl)
                            #print(" ")
                #if we found a new wall add (a reduced word for it) to the list
                #also need to look a layer deeper
                if parallel==False:
                    H.append(tuple(gRef.reduced_word()))
                    fin=False
        #increase the search radius
        n=n+1
    return H

                
#reflections seerating an element from the unit bring it closer, reflections act on group elements by left multiplication
#r and g are goup elements
def seperateFromOneElem(r,g):
    if (r*g).length()<g.length():
        return True
    else:
        return False


#find all the walls seperating g, that are not seperated from g by another wall
#G is the group, g an element of G, m the finite order of G
def wallsOfElem(G,g,m):
    #all walls seperating g from e are represented in (any) shortest representative
    l=g.length()
    w=g.reduced_word()
    #closest one is definitely one of them, initialize the list with that
    #another place where I may switch to elements instead of reduced words later
    h=G.from_reduced_word(w[:l-1])
    r=G.from_reduced_word([w[l-1]])
    #making the respective reflection
    ref=h*r*(h^-1)
    Wg=[]
    Wg.append(tuple(ref.reduced_word()))
    #work down, it is entirely possible for there to be a dry spell between the seperating walls
    #e.g. the points not in the polyhedra adjacent to the unit that still get sent to it by the voracious projection
    for i in range(l):
        #check if seperated by one closer
        parallel=False
        #previous version had a different upper bound for i, which had underflow issues
        #this can probably be removed again, but I'm just adding comments on this pass
        k=max(l-i-1,0)
        #build reflection
        h=G.from_reduced_word(w[:k])
        r=G.from_reduced_word([w[k]])
        ref=h*r*(h^-1)
        #check if it is a new one
        for rl in Wg:
            r2=G.from_reduced_word(rl)
            #check if we should not add
            if seperateFromOne(ref,r2,m):
                parallel=True
        if parallel==False:
            Wg.append(tuple(ref.reduced_word()))
    return Wg
        

#implementing the voracious projection
#G is the group, g an element of G, m the finite order of G
def voraciousProj(G,g,m):
    if g.is_one():
        return g
    Wg=wallsOfElem(G,g,m)
    lmin=len(Wg)
    #listing all the geodesics, going backwards on all of them we will encounter the voracious representation by seeing which one crosses all of Wg first
    Can=g.reduced_words()
    l=g.length()
    #the voracious projection is passed by one of the geodesic, since they have to pass |Wg| walls we skip ahead to that many steps into the process
    for i in range(lmin-1,l+1):
        #get the candidates of the specified lengths
        CanTemp=[]
        for h in Can:
            CanTemp.append(h[:l-i])
        #check if any of the candidates are seperated from g by all of Wg, i.e. none of Wg seperates the candidate from the unit
        for p in CanTemp:
            seperate=True
            for rl in Wg:
                r=G.from_reduced_word(rl)
                if seperateFromOneElem(r,G.from_reduced_word(p)):
                    seperate=False
            if seperate==True:
                return G.from_reduced_word(p)
        Can=CanTemp
    return g


#find the elements that have voracious projection to the unit
#G is the group, m it's finite order
def vorProjOne(G,m):
    projElem=[]
    done=False
    l=0
    #since the voracious projection preserves the ordering h\leq g iff there is a geodesic word for g starting with a geodesic word for h
    #we stop looking when we hit a radius where there are no new ones
    #this one can probably be drastically improved with that fact by being more restrictive with the candidates
    #that does require rewriting how we construct the candidate list
    while not done:
        done=True
        tempCand=G.elements_of_length(l)
        l=l+1
        for g in tempCand:
            if voraciousProj(G,g,m).is_one():
                projElem.append(g)
                done=False
    return projElem


#G is a group, A is a list of elements of G
def setInvert(G,A):
    B=[]
    for g in A:
        #g=G.from_reduced_word(g1)
        B.append(g^-1)
    return B


#G is the group, g an element of G, B a list of elements of G, it is the Garseid Shadow
#in this case the inverses of elements that project to the identity 
def shadowProj(G,g,B):
    cand=G.one()
    for h in B:
        if h.weak_le(g):
            if cand.length()<h.length():
                cand=h
    return cand



#Setting up the FSA, only establishing the states from the walls around the unit and setting them as accepting
#We only need the list of elements that are in the Shadow
def sSetupVorFSA(B):
    States=[]
    for u in B:
        #labels need to be hashable, and for our purposes not care about order, frozensets satisfy those conditions
        States.append(FSMState(u,is_final=True))
    SVorFSA=Automaton()
    SVorFSA.add_states(States)
    #moved this to the FSA construction, don't remember why, probably some bug
    #(VorFSA.state(frozenset(()))).is_initial=True
    return SVorFSA



#given the Coxeter matrix for our Coxeter group we want to build the FSA
def sConstructVorFSA(M):
    #construct the group and the walls
    W=CoxeterGroup(M)
    m=finiteOrder(W)
    A=vorProjOne(W,m)
    B=setInvert(W,A)
    #set up the states and the initial state
    SVFSA=sSetupVorFSA(B)
    #print(list(VFSA.states()))
    (SVFSA.state(W.one())).is_initial=True
    #loop over the points that give us our transitions
    for b in B:
        for g in B:
            l=g.length()
            if not(l==0):
                if (shadowProj(W,g*b,B)*(g^-1)).is_one():
                    StateOfg=SVFSA.state(g)
                    StateOfb=SVFSA.state(b)
                    Words=(g^-1).reduced_words()
                    l=len(Words[0])
                    for labels in Words:
                        #start this chain at the start
                        State1=StateOfb
                        for i in range(l-1):
                            #to make sure the states are distinct the label contains the start, the element, the word and how far into the word we are
                            State2=FSMState((g,StateOfb.label(),tuple(labels),i),is_final=False)
                            SVFSA.add_state(State2)
                            SVFSA.add_transition(FSMTransition(State1,State2,labels[i]))
                            #setup the next step in the chain
                            State1=State2
                        #connect the chain to the accept state
                        SVFSA.add_transition(FSMTransition(State1,StateOfg,labels[l-1]))
    #we calculated these and they are still useful
    return SVFSA, A, B


#this loops over the coefficients I want to use and makes the date for all the triangle groups (with coefficients increasig in the order of the list) and outputs a dictionary labeled with the tuple for the data
def sMakeData(listMatrix):
    t0=time.time()
    Data=dict()
    i=0
    for M in listMatrix:
        print(M)
        W=CoxeterGroup(M)
        #Find the order of all finite special subgroups
        print(finiteOrder(W))
        tStart=time.time()
        sFSA, A, B=sConstructVorFSA(M)
        print(len(B))
        tEnd=time.time()
        print(tEnd-tStart)
        Data[i]=(sFSA, W, A, B, tEnd-tStart)
        save((sFSA, W, A, B, tEnd-tStart),f"sFSAMatrixInput{i}")
        i=i+1
    t1=time.time()
    print(t1-t0)
    return Data

def threeMatrixTest():
    ListMatrix=[]
    Coeff=[2,3,4,5,6,-1]
    l=len(Coeff)
    for i in range(l):
        for j in range(i,l):
            for k in range(j,l):
                ListMatrix.append([[1,Coeff[i],Coeff[j]],[Coeff[i],1,Coeff[k]],[Coeff[j],Coeff[k],1]])
    return ListMatrix

tStart=time.time()
n=2
while (time.time()-tStart)<32400:
    t0=time.time()
    print(n)
    FSA, A, B = sConstructVorFSA([[1,2,2],[2,1,n],[2,n,1]])
    t1=time.time()
    save([FSA,A,B,t1-t0],f"Data22{n}")
    n=n+1