package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.IDawgLetter;

/**
 * DawgState containing information for the rename-and-reorder dawg transformation.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class RenameAndReorderDawgState<LETTER, COLNAMES> extends DawgState {


	private final IDawgLetter<LETTER> mLetter;

	private final COLNAMES mRightNeighbourColumn;

	private final DawgState mInnerState;

	public RenameAndReorderDawgState(final IDawgLetter<LETTER> letter, final COLNAMES column,
			final DawgState innerDawgState,
			final DawgState replacement) {
		super(replacement);
		this.mLetter = letter;
		this.mRightNeighbourColumn = column;
		this.mInnerState = innerDawgState;
	}

	/**
	 * An edge with this letter will be inserted in the new column
	 */
	public IDawgLetter<LETTER> getLetter() {
		return mLetter;
	}

	/**
	 * A column in the old Dawgs signature or null, indicating where the new column will be inserted.
	 * The states that are left of this column will be split.
	 * (this value being null means that the final states of the old dawg will be split.
	 */
	public COLNAMES getColumn() {
		return mRightNeighbourColumn;
	}

	/**
	 * We make different copies from the old-dawg's states between old and new column, this fields
	 * contains the original state that we copied from.
	 */
	public DawgState getInnerState() {
		return mInnerState;
	}

	@Override
	public String toString() {
		return String.format("RnRDawgState#%d(%s --> %s, %s)",
				this.hashCode() % 10000,
				mLetter,
				mRightNeighbourColumn,
				mInnerState.hashCode() % 10000);
	}
}