package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class BvultGraph {

	private final HashMap<Term, Vertex> vertices;


	public BvultGraph() {
		vertices = new HashMap<>();

	}

	public void addVertex(final Term vertex) {
		if (!vertices.containsKey(vertex)) {
			vertices.put(vertex, new Vertex(vertex));
		}

	}

	public Vertex getVertex(final Term vertex) {
		return vertices.get(vertex);
	}

	public void addEdge(final Vertex from, final Literal edge, final Vertex to) {
		from.addNeighbor(to, edge);
	}

	public void resetCycleVisited() {
		for (final Term vertexTerm : vertices.keySet()) {
			final Vertex vertex = vertices.get(vertexTerm);
			vertex.setBeingVisited(false);
			vertex.setVisited(false);
		}
	}


	public HashSet<Literal> getCycle(final Vertex sourceVertex) {
		System.out.println("ieter " + sourceVertex.getTerm());
		sourceVertex.setBeingVisited(true);
		final HashSet<Literal> circle = new HashSet<>();
		for (final Vertex neighbor : sourceVertex.getAdjacencyList().keySet()) {
			System.out.println("nachbarcheck " + neighbor.getTerm());
			if (neighbor.isBeingVisited()) {
				// backward edge exists
				circle.add(sourceVertex.getAdjacencyList().get(neighbor));

				return circle;
			} else if (!neighbor.isVisited()) {

				final HashSet<Literal> nieghborCircle = getCycle(neighbor);
				if (nieghborCircle != null) {
					if (!nieghborCircle.isEmpty()) {
						circle.addAll(nieghborCircle);
						circle.add(sourceVertex.getAdjacencyList().get(neighbor));
					}

				}
				System.out.println(circle);

			}
		}

		sourceVertex.setBeingVisited(false);
		sourceVertex.setVisited(true);
		return circle;
	}

}

class Vertex {

	private final Term label;
	private boolean beingVisited;
	private boolean visited;
	private final HashMap<Vertex, Literal> adjacencyList;

	public Vertex(final Term label) {
		this.label = label;
		adjacencyList = new HashMap<>();
	}

	public void addNeighbor(final Vertex adjacent, final Literal lit) {
		adjacencyList.put(adjacent, lit);
	}

	public void setBeingVisited(final boolean bool) {
		beingVisited = bool;
	}

	public void setVisited(final boolean bool) {
		visited = bool;
	}

	public Term getTerm() {
		return label;
	}

	public boolean isBeingVisited() {
		return beingVisited;
	}

	public boolean isVisited() {
		return visited;
	}

	public HashMap<Vertex, Literal> getAdjacencyList() {
		return adjacencyList;
	}
}

