import styled from 'styled-components';

const Styles = styled.div`

  padding: 1rem;

  .frozen {
    background: #f5f5f5;
    -webkit-user-select: none;
    -moz-user-select: none;
    user-select: none;
  }
  .rt-th.frozen {
    border-bottom: 1px solid #f8f8f8;
  }

  .table {
    // display: inline-block;
    // border-spacing: 0;
    // border: 1px solid black;

    .tr {
      background-color: #FFFFFF;
      :last-child {
        .td {
          // border-bottom: 0;
        }
      }
    }

    .th,
    .td {
      margin: 0;
      padding: 0;
      border: 1px solid #353535;
      background-color: #FFFFFF;
      :last-child {
        border-right: 1px solid black;
      }

      input {
        font-size: 1rem;
        padding: 0.5rem;
        margin: 0;
        border: 0;
        width: 100%;
        height: 100%;
      }
    }
  }
`

export {
    Styles,
}