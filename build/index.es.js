import { __assign, __makeTemplateObject } from 'tslib';
import React, { useMemo, useRef, useCallback, useState, useEffect } from 'react';
import { Button as Button$1 } from 'reactstrap';
import { CornerUpLeft, Download } from 'react-feather';
import { useTable, useBlockLayout } from 'react-table';
import { FixedSizeList } from 'react-window';
import styled from 'styled-components';

var scrollbarWidth = function () {
    // thanks too https://davidwalsh.name/detect-scrollbar-width
    var scrollDiv = document.createElement('div');
    scrollDiv.setAttribute('style', 'width: 100px; height: 100px; overflow: scroll; position:absolute; top:-9999px;');
    document.body.appendChild(scrollDiv);
    var scrollbarWidth = scrollDiv.offsetWidth - scrollDiv.clientWidth;
    document.body.removeChild(scrollDiv);
    return scrollbarWidth;
};

function styleInject(css, ref) {
  if ( ref === void 0 ) ref = {};
  var insertAt = ref.insertAt;

  if (!css || typeof document === 'undefined') { return; }

  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css_248z = "* {\n  box-sizing: border-box; }\n\nbody {\n  margin: 0;\n  font-family: \"Lato\", Arial;\n  font-size: 14px;\n  -webkit-font-smoothing: antialiased;\n  -moz-osx-font-smoothing: grayscale; }\n\ncode {\n  font-family: source-code-pro, Menlo, Monaco, Consolas, 'Courier New', monospace; }\n\n.react_table--wrapper {\n  margin-top: 30px;\n  overflow: hidden; }\n  .react_table--wrapper table {\n    border-spacing: 0;\n    border-collapse: collapse;\n    background-color: #fff; }\n  .react_table--wrapper thead {\n    background-color: #f7f7f7;\n    will-change: transform;\n    position: relative; }\n    .react_table--wrapper thead tr:last-child {\n      box-shadow: 0px 1px 3px 0px rgba(0, 0, 0, 0.15); }\n    .react_table--wrapper thead.fixed_thead {\n      top: 0;\n      position: fixed;\n      z-index: 10; }\n      .react_table--wrapper thead.fixed_thead + tbody:before,\n      .react_table--wrapper thead.fixed_thead + tbody:after {\n        content: \"\";\n        display: block;\n        background-color: #ffffff;\n        position: fixed;\n        top: 0;\n        left: 0;\n        width: 16px;\n        height: 73px; }\n        @media screen and (max-width: 1000px) {\n          .react_table--wrapper thead.fixed_thead + tbody:before,\n          .react_table--wrapper thead.fixed_thead + tbody:after {\n            display: none; } }\n      .react_table--wrapper thead.fixed_thead + tbody:after {\n        right: 0;\n        left: auto; }\n  .react_table--wrapper tbody tr:hover {\n    background-color: #f1f1f1; }\n  .react_table--wrapper tr {\n    outline: 0;\n    vertical-align: middle; }\n  .react_table--wrapper th {\n    position: relative;\n    font-weight: 700;\n    text-align: center;\n    white-space: nowrap;\n    color: #4b4b4b;\n    vertical-align: top;\n    will-change: transform;\n    width: 100px;\n    border: 1px solid #ccc;\n    background-color: #f0f0f0;\n    padding: 10px 10px; }\n    .react_table--wrapper th > div:first-child {\n      line-height: 26px; }\n  .react_table--wrapper td {\n    vertical-align: middle;\n    color: #4b4b4b;\n    border: 1px solid #353535;\n    background-color: #FFFFFF; }\n    .react_table--wrapper td > div:first-child {\n      min-width: 0;\n      text-align: center;\n      word-break: normal;\n      display: inline-table; }\n    .react_table--wrapper td input {\n      font-size: 1rem;\n      padding: 0.5rem;\n      margin: 0;\n      border: 0;\n      width: 100%;\n      height: 100%; }\n\n.pagination {\n  padding: 16px 32px;\n  background-color: #f7f7f7;\n  text-align: center; }\n\n.svg-icon {\n  display: inline-block;\n  fill: #a29060; }\n  .svg-icon--disabled {\n    cursor: default;\n    fill: #a7a9ac !important; }\n    .svg-icon--disabled:hover {\n      cursor: default;\n      opacity: 1; }\n  .svg-icon-info {\n    fill: #a7a9ac; }\n  .svg-icon.rotate-mirror {\n    transform: scaleX(-1) rotate(-90deg); }\n\n.custom-scroll {\n  display: none;\n  position: absolute;\n  height: 26px;\n  left: 0;\n  right: 0;\n  bottom: 28px;\n  padding: 9px 12px;\n  z-index: 1;\n  cursor: pointer;\n  background-color: #f7f7f7; }\n  .custom-scroll--active {\n    position: relative;\n    overflow: hidden !important;\n    padding-bottom: 32px; }\n    .custom-scroll--active .custom-scroll {\n      display: block; }\n  .custom-scroll--content {\n    height: 100%;\n    width: 100%;\n    overflow: hidden;\n    overflow-x: scroll;\n    overflow: -moz-scrollbars-none;\n    -ms-overflow-style: none; }\n    .custom-scroll--content::-webkit-scrollbar {\n      width: 0 !important; }\n  .custom-scroll-line {\n    background: #9fa1a4;\n    position: relative;\n    width: 80%;\n    height: 8px;\n    left: 0;\n    border-radius: 3px;\n    transition: 0.1s width ease-out;\n    min-width: 40px; }\n    .custom-scroll-line-container {\n      width: 100%;\n      position: relative;\n      overflow: hidden; }\n      .custom-scroll-line-container:before {\n        content: '';\n        position: absolute;\n        top: 0;\n        left: 0;\n        right: 0;\n        height: 8px;\n        background: #f7f7f7;\n        border-radius: 3px; }\n  .custom-scroll--fixed .custom-scroll {\n    position: fixed;\n    padding: 8px 24px;\n    background: #f7f7f7;\n    transition: 0.1s left ease-out;\n    bottom: 0px; }\n    .custom-scroll--fixed .custom-scroll-line-container:before {\n      background: #ffffff; }\n\n.td {\n  vertical-align: middle;\n  color: #4b4b4b;\n  border: 1px solid #ccc;\n  background-color: #FFFFFF; }\n  .td > div:first-child {\n    min-width: 0;\n    text-align: center;\n    word-break: normal;\n    display: inline-table; }\n  .td input {\n    font-size: 1rem;\n    padding: 0.5rem;\n    margin: 0;\n    border: 0;\n    width: 100%;\n    height: 100%; }\n\n.frozen {\n  background: #f5f5f5; }\n\n.contextMenu {\n  position: fixed;\n  background: white;\n  box-shadow: 0px 2px 10px #999999; }\n  .contextMenu--option {\n    padding: 6px 50px 5px 10px;\n    min-width: 160px;\n    cursor: default;\n    font-size: 12px; }\n    .contextMenu--option:hover {\n      background: linear-gradient(to top, #555, #333);\n      color: white; }\n    .contextMenu--option:active {\n      color: #e9e9e9;\n      background: linear-gradient(to top, #555, #444); }\n    .contextMenu--option__disabled {\n      color: #999999;\n      pointer-events: none; }\n  .contextMenu--separator {\n    width: 100%;\n    height: 1px;\n    background: #CCCCCC;\n    margin: 0 0 0 0; }\n\n.menu {\n  font-size: 14px;\n  background-color: #fff;\n  border-radius: 2px;\n  padding: 5px 0 5px 0;\n  width: 150px;\n  height: auto;\n  margin: 0;\n  position: absolute;\n  list-style: none;\n  box-shadow: 0 0 20px 0 #ccc; }\n\n.menu__item {\n  padding: 0.5em 1em;\n  color: #000;\n  cursor: pointer;\n  display: flex;\n  align-items: center; }\n\n.menu__item:hover {\n  background-color: #f2f2f2;\n  border-left: 4px solid #ccc; }\n\n.menu__icon {\n  margin-right: 8px; }\n\n.divider {\n  border-bottom: 1px solid #eee;\n  margin: 10px 0; }\n\n.context-sub-menu,\n.context-menu {\n  position: fixed;\n  background: #fff;\n  z-index: 9999999;\n  width: 120px;\n  margin: 0;\n  padding: 5px 0;\n  border-radius: 2px;\n  box-shadow: 0 0 6px rgba(0, 0, 0, 0.2);\n  font-size: 12px; }\n\n.context-menu .context-menu-item {\n  height: 30px;\n  display: flex;\n  align-items: center;\n  padding: 6px 10px;\n  cursor: pointer;\n  position: relative;\n  border-bottom: 1px solid #f2f2f2; }\n\n.context-menu .context-menu-item span {\n  display: block;\n  white-space: nowrap;\n  overflow: hidden;\n  text-overflow: ellipsis; }\n\n.context-menu-item:last-of-type {\n  border-bottom: none; }\n\n.context-menu .context-menu-item:hover {\n  background: #f2f2f2; }\n\n.context-menu .context-sub-menu {\n  position: absolute;\n  top: 0;\n  left: 100%;\n  display: none;\n  width: 100px; }\n\n.context-menu .context-menu-item:hover > .context-sub-menu {\n  display: block; }\n\n.context-menu.left .context-sub-menu {\n  left: 0;\n  transform: translateX(-100%); }\n\n.context-menu.top .context-sub-menu {\n  top: 100%;\n  transform: translateY(-100%); }\n\n.context-menu.left.top .context-sub-menu {\n  transform: translate(-100%, -100%); }\n";
styleInject(css_248z);

var NewTable = function (_a) {
    // Create an editable cell renderer
    var columns = _a.columns, data = _a.data, _b = _a.exportExcel, exportExcel = _b === void 0 ? false : _b, fileName = _a.fileName, resetData = _a.resetData, undoData = _a.undoData, saveChanges = _a.saveChanges;
    var EditableCell = function (_a) {
        var 
        // @ts-ignore
        initialValue = _a.value, index = _a.row.index, id = _a.column.id;
        // We need to keep and update the state of the cell normally
        var _b = useState(initialValue), value = _b[0], setValue = _b[1];
        var onChange = function (e) {
            setValue(e.target.value);
        };
        // We'll only update the external data when the input is blurred
        var onBlur = function () {
            //   updateMyData(index, id, value)
        };
        // If the initialValue is changed external, sync it up with our state
        useEffect(function () {
            setValue(initialValue);
        }, [initialValue]);
        if (id === 'MD') {
            return React.createElement("input", { value: value, onChange: onChange, onBlur: onBlur, className: 'frozen', readOnly: true });
        }
        else {
            return React.createElement("input", { value: value, onChange: onChange, onBlur: onBlur });
        }
        // return <input value={value}  onChange={onChange} onBlur={onBlur} />
    };
    var defaultColumn = {
        Cell: EditableCell,
    };
    var scrollBarSize = useMemo(function () { return scrollbarWidth(); }, []);
    // Use the state and functions returned from useTable to build your UI
    var _c = useTable({
        // @ts-ignore
        columns: columns,
        // @ts-ignore
        data: data,
        defaultColumn: defaultColumn
        // updateMyData 
    }, useBlockLayout), getTableProps = _c.getTableProps, getTableBodyProps = _c.getTableBodyProps, headerGroups = _c.headerGroups, rows = _c.rows, totalColumnsWidth = _c.totalColumnsWidth, prepareRow = _c.prepareRow;
    var tHeadRef = useRef();
    var tBodyRef = useRef();
    //   const doExportToExcel = useCallback(() => {
    //     const resultColumns = getColumns(columns, defaultColumn);
    //     const resultRows = getRows(rows, resultColumns);
    //     console.log('resultColumns', resultColumns);
    //     console.log('resultRows', resultRows);
    //     return exportToExcel(
    //       {
    //         sheet: {
    //           sheetName: fileName || "Excel Export",
    //           columns: resultColumns,
    //           rows: resultRows,
    //         },
    //       },
    //       `${fileName || "Excel_Export"}_${new Date().toLocaleDateString()}`,
    //     );
    //   }, [fileName, columns, defaultColumn, rows]);
    var RenderRow = useCallback(
    // @ts-ignore
    function (_a) {
        var index = _a.index, style = _a.style;
        var row = rows[index];
        prepareRow(row);
        return (React.createElement("div", __assign({}, row.getRowProps({
            style: style,
        }), { className: "tr" }), row.cells.map(function (cell, ind) {
            return (React.createElement("div", __assign({}, cell.getCellProps({
                // @ts-ignore
                className: "td " + cell.column.className
            })), cell.render('Cell')));
        })));
    }, [prepareRow, rows]);
    // const RenderRow = useCallback(
    //   ({ index, style }) => {
    //     const row = rows[index]
    //     prepareRow(row)
    //     return (
    //       <tr {...row.getRowProps()}>
    //         {row.cells.map((cell) => {
    //           return <td {...cell.getCellProps()}>{cell.render("Cell")}</td>;
    //         })}
    //       </tr>
    //     )
    //   },
    //   [prepareRow, rows]
    // )
    var react_table = useRef();
    return (React.createElement(React.Fragment, null,
        React.createElement(Button$1, { color: "primary", onClick: undoData, size: "md", className: "shadow-sm mr-1", "data-tip": true, "data-for": "UndoTip" },
            React.createElement(CornerUpLeft, { className: "feather", size: 30, style: { marginTop: "-5px" } }),
            React.createElement("span", { style: { padding: "5px" } }, "Undo")),
        React.createElement(Button$1, { color: "primary", onClick: saveChanges, "data-tip": true, "data-for": "SaveChangeTip", className: "shadow-sm mr-1" }, "Save Changes"),
        React.createElement(Button$1, { color: "primary", onClick: resetData, "data-tip": true, "data-for": "ResetTableTip", className: "shadow-sm mr-1" }, "Reset"),
        exportExcel &&
            (React.createElement(React.Fragment, null,
                React.createElement(Button$1, { color: "primary", "data-tip": true, "data-for": "ExcelTableTip", className: "shadow-sm" },
                    React.createElement(Download, { className: "feather", size: 30, style: { marginTop: "-5px" } }),
                    React.createElement("span", { style: { padding: "5px" } }, "Export Excel")))),
        React.createElement("div", { className: "react_table--wrapper", style: { marginTop: "30px" } },
            React.createElement("table", __assign({}, getTableProps(), { 
                // ref={react_table} 
                id: "react_table" }),
                React.createElement("thead", null, headerGroups.map(function (headerGroup) { return (React.createElement("tr", __assign({}, headerGroup.getHeaderGroupProps()), headerGroup.headers.map(function (column) {
                    // @ts-ignore
                    return column.hideHeader === false ? null : (React.createElement("th", __assign({}, column.getHeaderProps()), column.render("Header")));
                }))); })),
                React.createElement("tbody", __assign({}, getTableBodyProps()),
                    React.createElement(FixedSizeList, { height: 400, itemCount: rows.length, itemSize: 35, width: totalColumnsWidth + scrollBarSize }, RenderRow))))));
};

var Styles = styled.div(templateObject_1 || (templateObject_1 = __makeTemplateObject(["\n\n  padding: 1rem;\n\n  .frozen {\n    background: #f5f5f5;\n    -webkit-user-select: none;\n    -moz-user-select: none;\n    user-select: none;\n  }\n  .rt-th.frozen {\n    border-bottom: 1px solid #f8f8f8;\n  }\n\n  .table {\n    // display: inline-block;\n    // border-spacing: 0;\n    // border: 1px solid black;\n\n    .tr {\n      background-color: #FFFFFF;\n      :last-child {\n        .td {\n          // border-bottom: 0;\n        }\n      }\n    }\n\n    .th,\n    .td {\n      margin: 0;\n      padding: 0;\n      border: 1px solid #353535;\n      background-color: #FFFFFF;\n      :last-child {\n        border-right: 1px solid black;\n      }\n\n      input {\n        font-size: 1rem;\n        padding: 0.5rem;\n        margin: 0;\n        border: 0;\n        width: 100%;\n        height: 100%;\n      }\n    }\n  }\n"], ["\n\n  padding: 1rem;\n\n  .frozen {\n    background: #f5f5f5;\n    -webkit-user-select: none;\n    -moz-user-select: none;\n    user-select: none;\n  }\n  .rt-th.frozen {\n    border-bottom: 1px solid #f8f8f8;\n  }\n\n  .table {\n    // display: inline-block;\n    // border-spacing: 0;\n    // border: 1px solid black;\n\n    .tr {\n      background-color: #FFFFFF;\n      :last-child {\n        .td {\n          // border-bottom: 0;\n        }\n      }\n    }\n\n    .th,\n    .td {\n      margin: 0;\n      padding: 0;\n      border: 1px solid #353535;\n      background-color: #FFFFFF;\n      :last-child {\n        border-right: 1px solid black;\n      }\n\n      input {\n        font-size: 1rem;\n        padding: 0.5rem;\n        margin: 0;\n        border: 0;\n        width: 100%;\n        height: 100%;\n      }\n    }\n  }\n"])));
var PureTable = function (props) {
    var arr = props.Data;
    var nestedWell = props.HeaderWell;
    console.log('nestedWell', nestedWell);
    var Header = props.HeadersLogs;
    console.log('Header', Header);
    var cols = [];
    var rows = [];
    var columnsZero = [];
    cols.push({
        // @ts-ignore
        Header: nestedWell[0].label,
        hideHeader: props.hideHeader,
        columns: []
    });
    // console.log('cols before', cols);
    // @ts-ignore
    Header.forEach(function (item) {
        var currentCol = {};
        // @ts-ignore
        currentCol['Header'] = item;
        // @ts-ignore
        currentCol['accessor'] = item;
        if (item === 'MD') {
            // @ts-ignore
            currentCol['className'] = 'red';
        }
        columnsZero.push(currentCol);
    });
    // @ts-ignore
    cols[0]['columns'] = columnsZero;
    console.log('cols', cols);
    var _loop_1 = function (i) {
        var row = i;
        var currentRow2 = {};
        cols.map(function (d, index) {
            d.columns.map(function (c, index) {
                // @ts-ignore
                var valores = Number(arr[row][index]);
                // @ts-ignore
                currentRow2["" + c.accessor] = valores;
            });
        });
        rows.push(currentRow2);
    };
    // @ts-ignore 
    for (var i = 0; i < arr.length; i++) {
        _loop_1(i);
    }
    var _a = useState(rows), data = _a[0], setData = _a[1];
    var originalData = useState(data)[0];
    // Undo Table
    function undoData() {
        console.log("undo");
        // props.handleCurves();
    }
    // Save Table
    function saveChanges() {
        // console.log("saveChanges nestedHeaders", this.props.nestedHeaders);
        // let nested = this.props.nestedHeaders;
        // console.log("nested", nested);
        // let wellHeaders = nested[0];
        // let logHeaders = nested[1];
        // let wellColumns = [];
        // gets each column well header
        // wellHeaders.forEach((header) => {
        //   for (let i = 0; i < header.colspan; i++) {
        //     wellColumns.push(header.label);
        //   }
        // });
        // formatting json request for saving data in backend
        var payload = [];
        // for (let i = 0; i < logHeaders.length; i++) {
        //   let column = i;
        //   let well = wellColumns[column];
        //   let log = logHeaders[column];
        //   let wellData = payload.filter((wellData) => wellData.name === well)[0];
        //   let data =
        //     this.hotTableComponent.current.hotInstance.getDataAtCol(column);
        //   if (wellData) {
        //     if (!wellData.logs) {
        //       wellData.logs = [{ name: log, values: data }];
        //     } else {
        //       wellData.logs.push({ name: log, values: data });
        //     }
        //   } else {
        //     wellData = { well_name: well };
        //     wellData.logs = [{ name: log, values: data }];
        //     payload.push(wellData);
        //   }
        // }
        console.log("data antes de salvar", payload);
        // let data = { data: payload };
        // saveEditionData(data)
        //   .then((well_errors) => {
        //     if (well_errors.length === 0) {
        //       setTimeout(
        //         () =>
        //           this.showToastr(
        //             "success",
        //             "Changes were saved succesfully.",
        //             "Success!"
        //           ),
        //         300
        //       );
        //     } else {
        //       let formatted_errors = well_errors.join(", ");
        //       console.log(well_errors);
        //       setTimeout(
        //         () =>
        //           this.showToastr(
        //             "warning",
        //             `An error ocurred in following wells: ${formatted_errors}`,
        //             "Warning"
        //           ),
        //         300
        //       );
        //     }
        //   })
        //   .catch((error) => {
        //     setTimeout(
        //       () =>
        //         this.showToastr("error", "Error while saving changes.", "Error"),
        //       300
        //     );
        //   });
    }
    var resetData = function () { return setData(originalData); };
    return (React.createElement(React.Fragment, null,
        React.createElement(Styles, null,
            React.createElement(NewTable, { columns: cols, data: data, 
                //  updateMyData={updateMyData}
                resetData: resetData, exportExcel: true, fileName: "table", undoData: undoData, saveChanges: saveChanges }))));
};
var templateObject_1;

var Button = function (props) {
    return React.createElement("button", null, props.label);
};

export { Button, PureTable };
//# sourceMappingURL=index.es.js.map
