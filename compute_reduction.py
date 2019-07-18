from collections import OrderedDict
import Automata

#alpha=raw_input('Enter the alphabet: ')
#distr=[]
#n=int(raw_input('Enter how many components you want: '))
#for i in range(0, n):
#    x = raw_input('Enter each sub-alphabet: ')
#    distr.append(x)

####sim_distr(distr)
#print('The distribution you have entered is')    
#print(distr)

#print('you can check whether a distribution has a reduction by typing...')

#check whether a subalphabet sub1 is a subset of another subalphabet sub2
def inclusion(sub1, sub2):
    for i in range(0, len(sub1)):
        if not(sub1[i] in sub2):
            return 0
    return 1

#simplify a distribution by keeping only those maximal subalphabets
def sim_distr(distr):
    distrnew=distr
    distr_prime=[distrnew[0]]
    del distrnew[0]
    while len(distrnew)>0:
        flag=1
        val=[]
        for i in range (0, len(distr_prime)):
            if inclusion(distrnew[0], distr_prime[i]):
                flag=0
                break
            elif inclusion(distr_prime[i],distrnew[0]):
                val.append(distr_prime[i])
        if flag==1:
            distr_prime.append(distrnew[0])
        del distrnew[0]
        if not(val==[]):
            for i in range (0, len(val)):
                distr_prime.remove(val[i])
    return distr_prime    

#merge subalphabets indexed by ind_1 and ind_2 in distr        
def merge(distr,ind_1,ind_2):
    distrnew=distr
    news=distrnew[ind_1]+distrnew[ind_2]
    newslist=list(news)
    newsset=list(set(newslist))
    newsub=''.join(newsset)
    distrnew=distrnew+[newsub]
    return sim_distr(distrnew)


#check whether sub is a subset of some subalphabet in distr
def check_depend(sub, distr):
    flag=0
    for i in range(0, len(distr)):
        if inclusion(sub,distr[i]):
            flag=1
            break
    return flag

#check whether distr1 is lower than distr2
def check_small(distr1, distr2):
    distr1new=distr1
    flag=1
    while len(distr1new)>0:
        if not(check_depend(distr1new[0],distr2)):
            flag=0
            break
        distr1new=distr1new[1:]
    return flag

#compute the intersection of subalphabets sub1 and sub2
def det_insec(sub1,sub2):
    sub1set=list(sub1)
    sub2set=list(sub2)
    res=set(sub1set).intersection(sub2set)
    return res    #''.join(res)

#compute the shared symbols in distr
def compute_share(distr):
    em=set([])
    for i in range(0,len(distr)-1):
        for j in range(i+1, len(distr)):
            ints=det_insec(distr[i],distr[j])
            em=set(em).union(ints)
    return em

#check whether distr1 is equal to distr2
def check_equal(distr1, distr2):
    return check_small(distr1, distr2) and check_small(distr2, distr1)

#simplify the set of distributions 
def sim_disset(disset):
    if len(disset)==0:
        return disset
    else:
        disset_prime=[disset[0]]
        disset=disset[1:]
        while len(disset)>0:
            flag=1
            val=[]
            for i in range (0, len(disset_prime)):
                if check_small(disset_prime[i],disset[0]):
                    flag=0
                    break
                elif check_small(disset[0],disset_prime[i]):
                    val.append(disset_prime[i])
            if flag==1:
                disset_prime=disset_prime+[disset[0]]
            disset=disset[1:]
            if not(val==[]):
                for i in range (0, len(val)):
                    disset_prime.remove(val[i])               
        return disset_prime  

#compute the set of all minimall merged distributions    
def mini_merge(distr):
    disset=[]
    for i in range(0, len(distr)-1):
        for j in range(i+1,len(distr)):
            x=merge(distr,i,j)
            if len(x)>1:
                disset.append(x)
    return sim_disset(disset)

#compute the intersection of distr with sub in substitution
def intersect_dis(distr, sub):
    result=[]
    subset=list(sub)
    for i in range(0, len(distr)):
        newslist=list(distr[i])
        res=set(newslist).intersection(subset)
        if not(res==set([])):
            result=result+[''.join(res)]
    return result

#substitute distr1 into distr2
def substitution(distr1, distr2):
    rest=[]
    for i in range(0, len(distr2)):
        if inclusion(''.join(compute_share(distr1)), distr2[i]):
            new=distr2
            new=new[:i]+new[i+1:]
            new=new+intersect_dis(distr1,distr2[i])
            rest=rest+[sim_distr(new)]
    return rest

#substitute distr1 into distr2 and distr2 into distr1
def by_substitution(distr1, distr2):
    return substitution(distr1,distr2)+substitution(distr2,distr1)

#determine whether distr is in distrset
def inset(distr,distrset):
    for i in range(0, len(distrset)):
        if check_equal(distr, distrset[i]):
            return 1
    return 0
        
#compute the difference of distrset1 with respect to distrset2
def distin(distrset1, distrset2):
    distrset1new=distrset1
    p=[]
    while (len(distrset1new)>0):
        if not(inset(distrset1new[0],distrset2+p)):
            p=p+[distrset1new[0]]
        else:
            distrset1new=distrset1new[1:]
    return p

#substitution-based proof    
def sub_proof(distr,distrset):
    #dic=0
    flag=1
    for i in range(0, len(distrset)):
        if not(check_small(distr,distrset[i])):
            flag=0
            break
    if flag==0:
        return 0
    resta1=distrset
    resta2=[]
    ind=1
    for i in range(0,len(resta1)-1):
        for j in range(i+1, len(resta1)):
            h=by_substitution(resta1[i],resta1[j])
            if inset(distr, h):
                print('the number of sub is '+format(ind))
                return 1
            resta2=resta2+h
    resta2=distin(resta2,resta1)
    #if inset(distr,resta2):
    #    return 1
        #gives the proof sequence
    while (len(resta2)>0):
        ind=ind+1
        resta2old=resta2
        resta1old=resta1
        resta2=[]
        restal=resta1old+resta2old
        for i in range(0,len(resta1old)):
            for j in range(0, len(resta2old)):
                h=by_substitution(resta1old[i], resta2old[j])
                if inset(distr, h):
                    print('the number of sub is '+format(ind))
                    return 1
                resta2=resta2+h
        for i in range(0, len(resta2old)-1):
            for j in range (i+1, len(resta2old)):
                h=by_substitution(resta2old[i], resta2old[j])
                if inset(distr, h):
                    print('the number of sub is '+format(ind))
                    return 1
                resta2=resta2+h
        resta2=distin(resta2,resta1)
        #if inset(distr,resta1+resta2):
        #    dic=1
        #    break
    #if dic==1:
    #    return 1
        #gives the proof sequence
    #else:
    return 0

#substitution-based proof 2    
def sub_proof2(distr,distrset):
    dic=0
    flag=1
    for i in range(0, len(distrset)):
        if not(check_small(distr,distrset[i])):
            flag=0
            break
    if flag==0:
        return 0
    resta1=distrset
    resta2=[]
    for i in range(0,len(resta1)-1):
        for j in range(i+1, len(resta1)):
            resta2=resta2+by_substitution(resta1[i],resta1[j])
    resta2=distin(resta2,resta1)
    if inset(distr,resta2):
        return 1
        #gives the proof sequence
    while (len(resta2)>0):
        resta2old=resta2
        resta1old=resta1
        resta2=[]
        restal=resta1old+resta2old
        for i in range(0,len(resta1old)):
            for j in range(0, len(resta2old)):
                resta2=resta2+by_substitution(resta1old[i], resta2old[j])
        for i in range(0, len(resta2old)-1):
            for j in range (i+1, len(resta2old)):
                resta2=resta2+by_substitution(resta2old[i], resta2old[j])
        resta2=distin(resta2,resta1)
        if inset(distr,resta1+resta2):
            dic=1
            break
    if dic==1:
        return 1
        #gives the proof sequence
    else:
        return 0


def existsred(distr):
    sa=mini_merge(distr)
    return check_reduction(distr,sa)
    
        
#determine the existence of a reduction 3       
def existsred3(distr):
    sa=mini_merge(distr)      
    if sub_proof(distr,sa):
        print('%s has a reduction %s via substitution-based proof' %(distr, sa))
        return 
    else:
        print('we cannot show %s has a reduction via substitution-based proof' %(distr))
        if sub_proof(distr, all_merge(distr)):
            print('%s has a reduction %s via relaxed substitution-based proof' %(distr, sa))
        else:
            print('we cannot show %s has a reduction via relaxed substitution-based proof;' %(distr))
            print('we do not know whether %s has a reduction' %(distr))
            return

#determine the existence of a reduction 2        
def existsred2(distr):
    sa=mini_merge(distr)
    if sub_proof2(distr,sa):
        print('%s has a reduction %s via substitution-based proof' %(distr, sa))
        return 
    else:
        print('we cannot show %s has a reduction via substitution-based proof' %(distr))
        if sub_proof2(distr, all_merge(distr)):
            print('%s has a reduction %s via relaxed substitution-based proof' %(distr, sa))
        else:
            print('we cannot show %s has a reduction via relaxed substitution-based proof;' %(distr))
            print('we do not know whether %s has a reduction' %(distr))
            return

#remove duplicates in a set of distributions  
def removedup(distrset):
    if len(distrset)==0:
        return distrset
    else:
        distrsetnew=distrset
        distrset_prime=[distrsetnew[0]]
        distrsetnew=distrsetnew[1:]
        while (len(distrsetnew)>0):
            flag=1
            for i in range(0, len(distrset_prime)):
                if check_equal(distrsetnew[0],distrset_prime[i]):
                    flag=0
                    break
            if flag==1:
                distrset_prime=distrset_prime+[distrsetnew[0]]
            distrsetnew=distrsetnew[1:]
    return distrset_prime


#generate the set of all merged distributions
def all_merge(distr):
    rlist=r=mini_merge(distr)
    while (len(rlist)>0):
        z=mini_merge(rlist[0])
        r=r+z
        rlist=rlist[1:]
        rlist=rlist+z
    return removedup(r)


#generate the relaxed candidate reduction
def relax(distr,distrset):
    r=all_merge(distr)
    re=[]
    for i in range(0, len(distrset)):
        for j in range(0, len(r)):
            if check_small(distrset[i], r[j]):
                re=re+[r[j]]
    return removedup(re)

         
#strenghthened substitution-based proof
def relax_subproof(distr,distrset):
    flag=1
    for i in range(0, len(distrset)):
        if not(check_small(distr,distrset[i])):
            flag=0
            break
    if flag==0:
        return 0
    return sub_proof(distr,relax(distr,distrset))

#strenghthened substitution-based proof 2
def relax_subproof2(distr,distrset):
    flag=1
    for i in range(0, len(distrset)):
        if not(check_small(distr,distrset[i])):
            flag=0
            break
    if flag==0:
        return 0
    return sub_proof2(distr,relax(distr,distrset))

#compute meet of two distributions
def meet(distr1, distr2):
    new=[]
    for i in range(0, len(distr1)):
        for j in range(0, len(distr2)):
            new=new+[''.join(set(distr1[i]).intersection(set(distr2[j])))]
    return sim_distr(new)
   

#refutation based on meet equality
def refute_meet(distr, distrset):
    distrsetnew=distrset
    while (len(distrsetnew)>1):
        ca=meet(distrsetnew[0],distrsetnew[1])
        distrsetnew=distrsetnew[2:]
        distrsetnew=distrsetnew+[ca]
    if check_equal(distr,distrsetnew[0]):
        return 0  
    else:
        return 1  
        

#L_{cand} based refutation 1
def dependence_refute(distr,distrset):
    s=''
    for i in range(0, len(distr)):
        s=s+distr[i]
    alpha=list(set(list(s)))
    nfun={}
    for i in range(0, len(alpha)):
        nfun[alpha[i]]=[]
        for j in range (0, len(distr)):
            if not(inclusion(alpha[i],distr[j])):
                nfun[alpha[i]]=nfun[alpha[i]]+[j]
    for i in range(0, len(distrset)):
        if not(dependence_decom(distr,nfun,distrset[i],alpha)):
            return 0
    return 1
  
    
#check decomposability of L_{cand} with respect to distr1             
def dependence_decom(distr,nfun,distr1,alpha):
    dif=set(distr1)-set(distr)
    dif=list(dif)
    graph_distr1={}
    for i in range(0, len(alpha)):
        graph_distr1[alpha[i]]=[]
        for j in range(0,len(alpha)):
            if not(i==j) and check_depend(''.join([alpha[i],alpha[j]]),distr1):
                graph_distr1[alpha[i]]=graph_distr1[alpha[i]]+[alpha[j]]
    for i in range(0, len(dif)):
        bd=boundary(distr1, dif[i], alpha)
        if check_cover(nfun,distr1,bd, dif[i],alpha, graph_distr1,distr):
            return 1
    return 0

def check_cover(nfun,distr1,bd, sub,alpha, graph_distr1,distr):
    sub=list(sub)
    ext=set(alpha)-set(sub)
    ext=list(ext)
    setnode=bd+ext
    nodeToNodes={}
    for i in range(0, len(setnode)):
        if inclusion(setnode[i],bd):
            nodeToNodes[setnode[i]]=list(set(graph_distr1[setnode[i]]).intersection(set(ext)))
        if inclusion(setnode[i],ext):
            nodeToNodes[setnode[i]]=list(set(graph_distr1[setnode[i]]).intersection(set(setnode)))
    check={}
    for i in range(0, len(ext)):
        check[ext[i]]=[]
        for j in range(0, len(bd)):
            check[ext[i]]=check[ext[i]]+getAllSimplePaths(bd[j],ext[i],nodeToNodes)
    check_sat={}        
    for i in range(0, len(ext)):
        check_sat[ext[i]]=set([])
        for j in range(0, len(check[ext[i]])):
            check_sat[ext[i]]=check_sat[ext[i]].union(computepath(check[ext[i]][j],nfun,distr))
    for i in range(0, len(ext)):
        if not(check_sat[ext[i]]==set(range(0,len(distr)))):
            return 0
    return 1
        
    #for i in range(0, len(bd)):
    #    for j in range(0, len(ext)):
    #        check[]=getALLSimplePaths(bd[i],ext[j],nodeToNodes)

    #continue from here
    return 1
    #generate the graph
    # both bd and ext are lists
    #for i in range(0, len(ext)):
        #generate paths
def computepath(path,nfun,distr):
    d=set(range(0,len(distr)))
    for i in range(0, len(path)-1):
        d=d.intersection(set(nfun[path[i]]))
    return d
    
def getAllSimplePaths(originNode, targetNode, nodeToNodes):
    return helpGetAllSimplePaths(targetNode,
                                 [originNode],
                                 set(originNode),
                                 nodeToNodes,
                                 list())
 
#
# Return all distinct simple paths ending at "targetNode", continuing
# from "currentPath". "usedNodes" is useful so we can quickly skip
# nodes we have already added to "currentPath". When a new solution path
# is found, append it to "answerPaths" and return it.
#    
def helpGetAllSimplePaths(targetNode,
                          currentPath,
                          usedNodes,
                          nodeToNodes,
                          answerPaths):
    lastNode = currentPath[-1]
    if lastNode == targetNode:
        answerPaths.append(list(currentPath))
    else:
        for neighbor in nodeToNodes[lastNode]:
            if neighbor not in usedNodes:
                currentPath.append(neighbor)
                usedNodes.add(neighbor)
                helpGetAllSimplePaths(targetNode,
                                      currentPath,
                                      usedNodes,
                                      nodeToNodes,
                                      answerPaths)
                usedNodes.remove(neighbor)
                currentPath.pop()
    return answerPaths        


#compute boundary events
def boundary(distrin,sub,alpha):
    sub=list(sub)
    ext=set(alpha)-set(sub)
    ext=list(ext)
    bon=[]
    for i in range(0, len(sub)):
        flag=0
        for j in range(0, len(ext)):
            if check_depend(''.join([sub[i],ext[j]]), distrin):
                flag=1
                break
        if flag==1:
            bon=bon+[sub[i]]
    return bon

#reduction verification
def check_reduction(distr,distrset):
    if refute_meet(distr,distrset):
        print('the candidate reduction %s is refuted via meet equality' %(distrset))
        return 0
    if dependence_refute(distr,distrset):
        print('the candidate reduction %s is refuted via L_{cand}' %(distrset))
        return 0
    if sub_proof(distr,distrset):
        print('the candidate reduction %s is a reduction via substitution-based proof' %(distrset))
        return 1
    else:
        print('we cannot verify %s via substitution-based proof;' %(distrset))
        if relax_subproof(distr,distrset):
            print('however, the candidate reduction %s is a reduction via relaxed substitution-based proof' %(distrset))
            return 1
        else:
            print('we cannot verify %s via relaxed substitution-based proof;' %(distrset))
            print('we do not know whether %s is a reduction of %s' %(distrset, distr))
            return 2

#reduction verification 2
def check_reduction2(distr,distrset):
    if refute_meet(distr,distrset):
        print('the candidate reduction %s is refuted via meet equality' %(distrset))
        return
    if dependence_refute(distr,distrset):
        print('the candidate reduction %s is refuted via L_{cand}' %(distrset))
        return
    if sub_proof2(distr,distrset):
        print('the candidate reduction %s is a reduction via substitution-based proof' %(distrset))
        return
    else:
        print('we cannot verify %s via substitution-based proof;' %(distrset))
        if relax_subproof2(distr,distrset):
            print('however, the candidate reduction %s is a reduction via relaxed substitution-based proof' %(distrset))
            return
        else:
            print('we cannot verify %s via relaxed substitution-based proof;' %(distrset))
            print('we do not know whether %s is a reduction of %s' %(distrset, distr))
            return        

#greedy production

#recursive generation    


#generate random distribution        
