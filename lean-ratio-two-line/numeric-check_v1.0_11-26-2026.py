import sys; sys.setrecursionlimit(10000)
N=1<<20; u=[0]*(N+2); u[1],u[2],u[3]=1,2,3
for n in range(4,N+2): k=n//2; u[n]=2*u[k]+(u[k+1] if n%2 else 0)
S={1,11,15}|{2**a+1 for a in range(1,21)}|{3*2**a+1 for a in range(1,20)}
bad=[n for n in range(1,N,2) if (u[n]<2*n)!=(n in S)]
print("iff mismatches:",bad[:10], "eq2n:",[n for n in range(1,N) if u[n]==2*n][:5])
print("a=0 checks: u(2)=",u[2],"(2^1-1=1)  u(4)=",u[4],"(2*(3-1)=4)")
