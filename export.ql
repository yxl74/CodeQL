import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest
import codeql.xml.Xml

class AndroidManifestFile extends XmlFile {
  AndroidManifestFile() {
    this.getBaseName() = "AndroidManifest.xml"
  }
}

class AndroidComponent extends Class {
  AndroidComponent() {
    this.getASupertype*().hasQualifiedName("android.app", [
      "Activity",
      "Service",
      "BroadcastReceiver",
      "ContentProvider"
    ])
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder")
  }

  string getComponentType() {
    this.getASupertype*().hasQualifiedName("android.app", "Activity") and result = "activity"
    or
    this.getASupertype*().hasQualifiedName("android.app", "Service") and result = "service"
    or
    this.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver") and result = "receiver"
    or
    this.getASupertype*().hasQualifiedName("android.content", "ContentProvider") and result = "provider"
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder") and result = "binder"
  }
}

predicate isExportedInAnyManifest(AndroidComponent component) {
  exists(AndroidManifestFile manifest, XmlElement elem |
    elem.getFile() = manifest and
    elem.getName() = component.getComponentType() and
    (
      elem.getAttributeValue("android:name") = component.getName()
      or
      elem.getAttributeValue("android:name") = component.getName().suffix(component.getPackage().getName().length() + 1)
    ) and
    (
      elem.getAttributeValue("android:exported") = "true"
      or
      (
        not elem.getAttributeValue("android:exported") = "false" and
        exists(XmlElement intentFilter |
          intentFilter.getParent() = elem and
          intentFilter.getName() = "intent-filter"
        )
      )
    )
  )
}

predicate isDynamicallyRegisteredOrStarted(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName([
      "registerReceiver", 
      "registerContentProvider",
      "startService",
      "bindService",
      "startActivity",
      "startActivityForResult"
    ]) and
    (
      mc.getAnArgument().getType() = component
      or
      mc.getAnArgument().(VarAccess).getVariable().getType() = component
    )
  )
}

predicate isRegisteredWithServiceManager(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName("addService") and
    mc.getMethod().getDeclaringType().hasQualifiedName("android.os", "ServiceManager") and
    (
      mc.getArgument(1).getType() = component
      or
      mc.getArgument(1).(VarAccess).getVariable().getType() = component
      or
      exists(CastExpr ce |
        ce = mc.getArgument(1) and
        ce.getExpr().getType() = component
      )
    )
  )
}

predicate isIntentTarget(AndroidComponent component) {
  exists(ClassInstanceExpr newIntent |
    newIntent.getConstructedType().hasQualifiedName("android.content", "Intent") and
    newIntent.getAnArgument().getType() = component
  )
}

predicate isUsedInPendingIntent(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
    mc.getAnArgument().getType() = component
  )
}

from AndroidComponent component
where
  isExportedInAnyManifest(component)
  or
  isDynamicallyRegisteredOrStarted(component)
  or
  isRegisteredWithServiceManager(component)
  or
  isIntentTarget(component)
  or
  isUsedInPendingIntent(component)
select 
  component,
  "This component is potentially exposed to external interactions. Reason: " +
  concat(string reason |
    (
      isExportedInAnyManifest(component) and
      reason = "Exported in a manifest file (explicitly or implicitly due to intent filter). "
    ) or (
      isDynamicallyRegisteredOrStarted(component) and
      reason = "Dynamically registered or started. "
    ) or (
      isRegisteredWithServiceManager(component) and
      reason = "Registered with ServiceManager.addService. "
    ) or (
      isIntentTarget(component) and
      reason = "Used as an Intent target. "
    ) or (
      isUsedInPendingIntent(component) and
      reason = "Used in a PendingIntent. "
    )
    |
    reason
  ) +
  "Verify if this exposure is intentional and properly secured."