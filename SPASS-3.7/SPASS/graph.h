/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                       GRAPHS                           * */
/* *                                                        * */
/* *  $Module:   GRAPH                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1998, 2001 MPI fuer Informatik          * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the FreeBSD    * */
/* *  Licence.                                              * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the LICENCE file       * */ 
/* *  for more details.                                     * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 1.2 $                                     * */
/* $State: Exp $                                            * */
/* $Date: 2010-02-22 14:09:58 $                             * */
/* $Author: weidenb $                                         * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: spass@mpi-inf.mpg.de                * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


/* $RCSfile: graph.h,v $ */

#ifndef _GRAPH_
#define _GRAPH_

#include "list.h"

typedef struct {
  NAT     number;
  int     dfs_num;
  int     comp_num;  /* completion number */
  POINTER info;      /* user defined information */
  LIST    neighbors;
} GRAPHNODE_STRUCT, *GRAPHNODE;

typedef struct {
  NAT  size;       /* number of nodes */
  LIST nodes;      /* list of GRAPHNODES */
  NAT  dfscount;   /* used for DFS */
  NAT  compcount;  /* used for DFS */
} GRAPH_STRUCT, *GRAPH;

static __inline__ NAT graph_NodeNumber(GRAPHNODE Node)
{
  return Node->number;
}

static __inline__ int graph_NodeDfsNum(GRAPHNODE Node)
{
  return Node->dfs_num;
}

static __inline__ void graph_NodeSetDfsNum(GRAPHNODE Node, int Number)
{
  Node->dfs_num = Number;
}

static __inline__ int graph_NodeCompNum(GRAPHNODE Node)
{
  return Node->comp_num;
}

static __inline__ void graph_NodeSetCompNum(GRAPHNODE Node, int Number)
{
  Node->comp_num = Number;
}

static __inline__ LIST graph_NodeNeighbors(GRAPHNODE Node)
{
  return Node->neighbors;
}

static __inline__ POINTER graph_NodeInfo(GRAPHNODE Node)
{
  return Node->info;
}

static __inline__ void graph_NodeSetInfo(GRAPHNODE Node, POINTER Info)
{
  Node->info = Info;
}

static __inline__ NAT graph_NodeOutdegree(GRAPHNODE Node)
{
  return list_Length(graph_NodeNeighbors(Node));
}

static __inline__ BOOL graph_NodeVisited(GRAPHNODE Node)
{
  return graph_NodeDfsNum(Node) >= 0;
}

static __inline__ BOOL graph_NodeCompleted(GRAPHNODE Node)
{
  return graph_NodeCompNum(Node) >= 0;
}

static __inline__ NAT graph_Size(GRAPH Graph)
{
  return Graph->size;
}

static __inline__ LIST graph_Nodes(GRAPH Graph)
{
  return Graph->nodes;
}

GRAPH     graph_Create(void);
void      graph_Delete(GRAPH);

GRAPHNODE graph_GetNode(GRAPH, NAT);
GRAPHNODE graph_AddNode(GRAPH, NAT);

void      graph_AddEdge(GRAPHNODE, GRAPHNODE);
void      graph_DeleteEdge(GRAPHNODE, GRAPHNODE);
void      graph_DeleteDuplicateEdges(GRAPH);

void      graph_SortNodes(GRAPH, BOOL (*)(GRAPHNODE, GRAPHNODE));
NAT       graph_StronglyConnectedComponents(GRAPH);

void      graph_NodePrint(GRAPHNODE Node);
void      graph_Print(GRAPH);

#endif
