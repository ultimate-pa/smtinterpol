package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class BvultGraph {

	private final HashMap<Term, Vertex> mVertices;


	public BvultGraph() {
		mVertices = new HashMap<>();

	}

	public void addVertex(final Term vertex) {
		if (!mVertices.containsKey(vertex)) {
			mVertices.put(vertex, new Vertex(vertex));
		}

	}

	public Vertex getVertex(final Term vertex) {
		return mVertices.get(vertex);
	}

	public void addEdge(final Vertex from, final Literal edge, final Vertex to) {
		from.addNeighbor(to, edge);
	}

	public void resetCycleVisited() {
		for (final Term vertexTerm : mVertices.keySet()) {
			final Vertex vertex = mVertices.get(vertexTerm);
			vertex.setBeingVisited(false);
			vertex.setVisited(false);
		}
	}


	public HashSet<Literal> getCycle(final Vertex sourceVertex) {
		sourceVertex.setBeingVisited(true);
		final HashSet<Literal> circle = new HashSet<>();
		for (final Entry<Vertex, Literal> neighbor : sourceVertex.getAdjacencyList().entrySet()) {
			// übers entry set iterieren, spart getAdjacencyList().get(neighbor)
			if (neighbor.getKey().isBeingVisited()) {
				// circle closed
				circle.add(neighbor.getValue());
				return circle;
			} else if (!neighbor.getKey().isVisited()) {
				final HashSet<Literal> neighborCircle = getCycle(neighbor.getKey());
				if (neighborCircle != null) {
					if (!neighborCircle.isEmpty()) {
						circle.addAll(neighborCircle);
						circle.add(neighbor.getValue());
					}

				}

			}
		}

		sourceVertex.setBeingVisited(false);
		sourceVertex.setVisited(true);
		return circle;
	}

}

class Vertex {

	private final Term mLabel;
	private boolean mBeingVisited;
	private boolean mVisited;
	private final HashMap<Vertex, Literal> mAdjacencyList;

	public Vertex(final Term label) {
		mLabel = label;
		mAdjacencyList = new HashMap<>();
	}

	public void addNeighbor(final Vertex adjacent, final Literal lit) {
		mAdjacencyList.put(adjacent, lit);
	}

	public void removeNeighbor(final Vertex adjacent, final Literal lit) {
		assert mAdjacencyList.containsKey(adjacent);
		assert mAdjacencyList.get(adjacent).equals(lit);
		mAdjacencyList.remove(adjacent);
	}

	public void setBeingVisited(final boolean bool) {
		mBeingVisited = bool;
	}

	public void setVisited(final boolean bool) {
		mVisited = bool;
	}

	public Term getTerm() {
		return mLabel;
	}

	public boolean isBeingVisited() {
		return mBeingVisited;
	}

	public boolean isVisited() {
		return mVisited;
	}

	public HashMap<Vertex, Literal> getAdjacencyList() {
		return mAdjacencyList;
	}
}

