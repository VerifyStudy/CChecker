from collections import defaultdict
graph = defaultdict(list)
graph[0].append(1)
graph[0].append(2)
graph[0].append(3)
graph[2].append(0)
graph[2].append(1)
graph[1].append(3)
print(graph)


def printAllPathsUtil(u, d, visited, path): 

    # Mark the current node as visited and store in path 
    visited[u]= True
    path.append(u) 

    # If current vertex is same as destination, then print 
    # current path[] 
    if u == d: 
        print(path) 
    else: 
        # If current vertex is not destination 
        # Recur for all the vertices adjacent to this vertex 
        for i in graph[u]: 
            if visited[i]== False: 
                printAllPathsUtil(i, d, visited, path) 
                    
    # Remove current vertex from path[] and mark it as unvisited 
    path.pop() 
    visited[u]= False
   
   
# Prints all paths from 's' to 'd' 
def printAllPaths(s, d): 

    # Mark all the vertices as not visited 
    visited =[False]*4 

    # Create an array to store paths 
    path = [] 

    # Call the recursive helper function to print all paths 
    printAllPathsUtil(s, d, visited, path) 
   

   
s = 2 ; d = 3
print("Following are all different paths from % d to % d :" %(s, d)) 
printAllPaths(s, d) 